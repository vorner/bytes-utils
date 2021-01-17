use std::borrow::{Borrow, BorrowMut, Cow};
use std::cmp::Ordering;
use std::convert::{Infallible, TryFrom};
use std::error::Error;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult, Write};
use std::hash::{Hash, Hasher};
use std::iter::{self, FromIterator};
use std::ops::{Add, AddAssign, Deref, DerefMut, Index, IndexMut};
use std::str::{self, FromStr};

use bytes::{Bytes, BytesMut};
use either::Either;

#[derive(Copy, Clone, Debug)]
pub struct Utf8Error<S> {
    e: str::Utf8Error,
    inner: S,
}

impl<S> Utf8Error<S> {
    pub fn into_inner(self) -> S {
        self.inner
    }
    pub fn from_utf8_error(&self) -> str::Utf8Error {
        self.e
    }
}

impl<S> Display for Utf8Error<S> {
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult {
        Display::fmt(&self.e, fmt)
    }
}

impl<S: Debug> Error for Utf8Error<S> {}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Direction {
    Forward,
    Backward,
}

#[derive(Clone, Debug)]
pub struct BytesIter<S, F> {
    bytes: Option<S>,
    extract: F,
    direction: Direction,
}

impl<S, F> BytesIter<S, F>
where
    S: Storage,
    F: FnMut(&str) -> Option<(usize, usize)>,
{
    pub fn new(s: StrInner<S>, direction: Direction, ext: F) -> Self {
        Self {
            bytes: Some(s.0),
            extract: ext,
            direction,
        }
    }
}

impl<S, F> Iterator for BytesIter<S, F>
where
    S: Storage,
    F: FnMut(&str) -> Option<(usize, usize)>,
{
    type Item = StrInner<S>;

    fn next(&mut self) -> Option<StrInner<S>> {
        let storage = self.bytes.take()?;
        // Safety: we keep sure it is valid UTF8 on the API boundary.
        let whole_str = unsafe { str::from_utf8_unchecked(storage.as_ref()) };
        fn split<S: Storage>(storage: S, left: usize, right: usize) -> (S, S) {
            let whole_str = unsafe { str::from_utf8_unchecked(storage.as_ref()) };
            // Sanity-check we are not slicing in the middle of utf8 code point. This would
            // panic if we do. It would also panic if we are out of range, which is also good.
            let _start = &whole_str[..left];
            let _end = &whole_str[right..];

            // Now that we are sure this is legal, we are going to slice the byte data for real.
            let (with_sep, end) = storage.split_at(right);
            let (start, _sep) = with_sep.split_at(left);
            (start, end)
        }
        match ((self.extract)(whole_str), self.direction) {
            (Some((chunk_end, sep_end)), Direction::Forward) => {
                assert!(chunk_end <= sep_end);
                let (start, end) = split(storage, chunk_end, sep_end);

                self.bytes = Some(end);
                Some(StrInner(start))
            }
            (Some((chunk_start, sep_start)), Direction::Backward) => {
                assert!(sep_start <= chunk_start);
                let (start, end) = split(storage, sep_start, chunk_start);

                self.bytes = Some(start);
                Some(StrInner(end))
            }
            (None, _) => {
                // No separator found -> return the whole rest (and keep None in ourselves)
                Some(StrInner(storage))
            }
        }
    }
}

fn sep_find<F: Fn(char) -> bool>(s: &str, is_sep: F) -> Option<(usize, usize)> {
    let sep_start = s.find(&is_sep)?;
    let sep_end = s[sep_start..]
        .find(|c| !is_sep(c))
        .map(|e| e + sep_start)
        .unwrap_or_else(|| s.len());
    Some((sep_start, sep_end))
}

fn empty_seps(s: &str, limit: usize) -> Option<(usize, usize)> {
    let char_end = s
        .char_indices()
        .skip(1)
        .map(|(i, _)| i)
        .chain(iter::once(s.len()).take((s.len() > 0) as usize))
        .take(limit)
        .next()?;
    Some((char_end, char_end))
}

fn rempty_seps(s: &str, limit: usize) -> Option<(usize, usize)> {
    let char_start = s
        .char_indices()
        .rev()
        .map(|(i, _)| i)
        .take(limit)
        .next()?;
    Some((char_start, char_start))
}

pub unsafe trait Storage: AsRef<[u8]> + Default + Sized {
    type Creator: Default + StorageMut;
    fn from_creator(creator: Self::Creator) -> Self;
    fn split_at(self, at: usize) -> (Self, Self);
}

unsafe impl Storage for Bytes {
    type Creator = BytesMut;
    fn from_creator(creator: Self::Creator) -> Self {
        creator.freeze()
    }
    fn split_at(mut self, at: usize) -> (Self, Self) {
        let right = self.split_off(at);
        (self, right)
    }
}

unsafe impl Storage for BytesMut {
    type Creator = BytesMut;
    fn from_creator(creator: Self::Creator) -> Self {
        creator
    }
    fn split_at(mut self, at: usize) -> (Self, Self) {
        let right = self.split_off(at);
        (self, right)
    }
}

pub unsafe trait StorageMut: Storage + AsMut<[u8]> {
    type Immutable: Storage;
    fn into_immutable(self) -> Self::Immutable;
    fn push_slice(&mut self, s: &[u8]);
}

unsafe impl StorageMut for BytesMut {
    type Immutable = Bytes;
    fn into_immutable(self) -> Self::Immutable {
        self.freeze()
    }
    fn push_slice(&mut self, s: &[u8]) {
        self.extend_from_slice(s)
    }
}

#[derive(Copy, Clone, Default)]
pub struct StrInner<S>(S);

impl<S: Storage> StrInner<S> {
    pub fn into_inner(self) -> S {
        self.0
    }
    pub fn inner(&self) -> &S {
        &self.0
    }
    pub fn from_inner(s: S) -> Result<Self, Utf8Error<S>> {
        match str::from_utf8(s.as_ref()) {
            Ok(_) => Ok(Self(s)),
            Err(e) => Err(Utf8Error { e, inner: s }),
        }
    }
    pub unsafe fn from_inner_unchecked(s: S) -> Self {
        Self(s)
    }

    pub fn split_at_bytes(self, at: usize) -> (Self, Self) {
        let (l, r) = self.0.split_at(at);
        (Self(l), Self(r))
    }

    // TODO: Make type public?
    pub fn split_whitespace_bytes(self) -> impl Iterator<Item = Self> {
        BytesIter::new(self, Direction::Forward, |s| sep_find(s, char::is_whitespace))
            .filter(|s| !s.is_empty())
    }

    pub fn split_ascii_whitespace_bytes(self) -> impl Iterator<Item = Self> {
        BytesIter::new(self, Direction::Forward, |s| sep_find(s, |c| {
                c.is_ascii() && (c as u8).is_ascii_whitespace()
            }))
            .filter(|s| !s.is_empty())
    }

    pub fn lines_bytes(self) -> impl Iterator<Item = Self> {
        if self.is_empty() {
            Either::Left(iter::empty())
        } else {
            let iter = BytesIter::new(self, Direction::Forward, |s| sep_find(s, |c| c == '\n'))
                .map(|s| match s.chars().next() {
                    Some('\r') => s.split_at_bytes(1).1,
                    _ => s,
                });
            Either::Right(iter)
        }
    }

    // TODO: Pattern API? :-(
    pub fn split_bytes<'s>(self, sep: &'s str) -> impl Iterator<Item = Self> + 's
    where
        S: 's,
    {
        if sep.is_empty() {
            let bulk = BytesIter::new(self, Direction::Forward, |s| empty_seps(s, usize::MAX));
            Either::Left(iter::once(Self::default()).chain(bulk))
        } else {
            let sep_find = move |s: &str| {
                s.find(sep).map(|pos| (pos, pos + sep.len()))
            };
            Either::Right(BytesIter::new(self, Direction::Forward, sep_find))
        }
    }

    pub fn splitn_bytes<'s>(self, mut n: usize, sep: &'s str) -> impl Iterator<Item = Self> + 's
    where
        S: 's,
    {
        // TODO: This seems to work, but is ugly. Any idea how to simplify?
        if sep.is_empty() {
            if n <= 1 {
                Either::Left(Either::Left(iter::once(self).take(n)))
            } else {
                n -= 1;
                let bulk = BytesIter::new(self, Direction::Forward, move |s| {
                    n -= 1;
                    empty_seps(s, n)
                });
                Either::Left(Either::Right(iter::once(Self::default()).chain(bulk)))
            }
        } else {
            let sep_find = move |s: &str| {
                n -= 1;
                if n == 0 {
                    None
                } else {
                    s.find(sep).map(|pos| (pos, pos + sep.len()))
                }
            };
            Either::Right(BytesIter::new(self, Direction::Forward, sep_find).take(n))
        }
    }

    pub fn rsplit_bytes<'s>(self, sep: &'s str) -> impl Iterator<Item = Self> + 's
    where
        S: 's,
    {
        if sep.is_empty() {
            let bulk = BytesIter::new(self, Direction::Backward, |s| rempty_seps(s, usize::MAX));
            Either::Left(iter::once(Self::default()).chain(bulk))
        } else {
            let sep_find = move |s: &str| {
                s.rfind(sep).map(|pos| (pos + sep.len(), pos))
            };
            Either::Right(BytesIter::new(self, Direction::Backward, sep_find))
        }
    }

    pub fn rsplitn_bytes<'s>(self, mut n: usize, sep: &'s str) -> impl Iterator<Item = Self> + 's
    where
        S: 's,
    {
        // TODO: This seems to work, but is ugly. Any idea how to simplify?
        if sep.is_empty() {
            if n <= 1 {
                Either::Left(Either::Left(iter::once(self).take(n)))
            } else {
                n -= 1;
                let bulk = BytesIter::new(self, Direction::Backward, move |s| {
                    n -= 1;
                    rempty_seps(s, n)
                });
                Either::Left(Either::Right(iter::once(Self::default()).chain(bulk)))
            }
        } else {
            let sep_find = move |s: &str| {
                n -= 1;
                if n == 0 {
                    None
                } else {
                    s.rfind(sep).map(|pos| (pos + sep.len(), pos))
                }
            };
            Either::Right(BytesIter::new(self, Direction::Backward, sep_find).take(n))
        }
    }
}

impl<S: StorageMut> StrInner<S> {
    pub fn push_str(&mut self, s: &str) {
        self.0.push_slice(s.as_bytes());
    }
    pub fn push(&mut self, c: char) {
        self.push_str(c.encode_utf8(&mut [0; 4]));
    }
    pub unsafe fn inner_mut(&mut self) -> &mut S {
        &mut self.0
    }
    pub fn freeze(self) -> StrInner<S::Immutable> {
        StrInner(self.0.into_immutable())
    }
}

impl<S: Storage> Deref for StrInner<S> {
    type Target = str;

    fn deref(&self) -> &str {
        unsafe { str::from_utf8_unchecked(self.0.as_ref()) }
    }
}

impl<S: StorageMut> DerefMut for StrInner<S> {
    fn deref_mut(&mut self) -> &mut str {
        unsafe { str::from_utf8_unchecked_mut(self.0.as_mut()) }
    }
}

impl<S, T> AsRef<T> for StrInner<S>
where
    S: Storage,
    str: AsRef<T>,
{
    fn as_ref(&self) -> &T {
        self.deref().as_ref()
    }
}

impl<S: StorageMut> AsMut<str> for StrInner<S> {
    fn as_mut(&mut self) -> &mut str {
        self.deref_mut()
    }
}

impl<S: Storage> Borrow<str> for StrInner<S> {
    fn borrow(&self) -> &str {
        self.deref()
    }
}

impl<S: StorageMut> BorrowMut<str> for StrInner<S> {
    fn borrow_mut(&mut self) -> &mut str {
        self.deref_mut()
    }
}

impl<S: Storage> Debug for StrInner<S> {
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult {
        Debug::fmt(self.deref(), fmt)
    }
}

impl<S: Storage> Display for StrInner<S> {
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult {
        Display::fmt(self.deref(), fmt)
    }
}

impl<S: Storage> Hash for StrInner<S> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.deref().hash(state)
    }
}

impl<S, I> Index<I> for StrInner<S>
where
    S: Storage,
    str: Index<I>,
{
    type Output = <str as Index<I>>::Output;

    fn index(&self, index: I) -> &Self::Output {
        self.deref().index(index)
    }
}

impl<S, I> IndexMut<I> for StrInner<S>
where
    S: StorageMut,
    str: IndexMut<I>,
{
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        self.deref_mut().index_mut(index)
    }
}

impl<S: StorageMut> Add<&str> for StrInner<S> {
    type Output = Self;

    fn add(mut self, rhs: &str) -> Self::Output {
        self.push_str(rhs);
        self
    }
}

impl<S: StorageMut> AddAssign<&str> for StrInner<S> {
    fn add_assign(&mut self, rhs: &str) {
        self.push_str(rhs);
    }
}

impl<S: StorageMut> Extend<char> for StrInner<S> {
    fn extend<T: IntoIterator<Item = char>>(&mut self, iter: T) {
        for c in iter {
            self.push(c);
        }
    }
}

impl<'a, S: StorageMut> Extend<&'a char> for StrInner<S> {
    fn extend<T: IntoIterator<Item = &'a char>>(&mut self, iter: T) {
        for c in iter {
            self.push(*c);
        }
    }
}

macro_rules! e {
    ($ty: ty) => {
        impl<'a, S: StorageMut> Extend<$ty> for StrInner<S> {
            fn extend<T: IntoIterator<Item = $ty>>(&mut self, iter: T) {
                for i in iter {
                    self.push_str(i.as_ref());
                }
            }
        }

        impl<'a, S> FromIterator<$ty> for StrInner<S>
        where
            S: Storage,
        {
            fn from_iter<T: IntoIterator<Item = $ty>>(iter: T) -> Self {
                let mut creator = StrInner(S::Creator::default());
                creator.extend(iter);
                StrInner(S::from_creator(creator.0))
            }
        }

        impl<'a, S> From<$ty> for StrInner<S>
        where
            S: Storage,
        {
            fn from(s: $ty) -> Self {
                iter::once(s).collect()
            }
        }

    };
}

e!(String);
e!(&'a String);
e!(Box<str>);
e!(&'a str);
e!(Cow<'a, str>);

macro_rules! t {
    ($ty: ty) => {
        impl TryFrom<$ty> for StrInner<$ty> {
            type Error = Utf8Error<$ty>;
            fn try_from(s: $ty) -> Result<Self, Utf8Error<$ty>> {
                Self::from_inner(s)
            }
        }

        impl From<StrInner<$ty>> for $ty {
            fn from(s: StrInner<$ty>) -> $ty {
                s.0
            }
        }
    }
}

t!(Bytes);
t!(BytesMut);

impl From<StrMut> for Str {
    fn from(s: StrMut) -> Self {
        s.freeze()
    }
}

impl<S: Storage> FromStr for StrInner<S> {
    type Err = Infallible;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(s.into())
    }
}

impl<S: Storage> PartialEq for StrInner<S> {
    fn eq(&self, other: &Self) -> bool {
        self.deref() == other.deref()
    }
}

impl<S: Storage> Eq for StrInner<S> {}

impl<S: Storage> PartialOrd for StrInner<S> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(Ord::cmp(self, other))
    }
}

impl<S: Storage> Ord for StrInner<S> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.deref().cmp(other.deref())
    }
}

macro_rules! c {
    ($ty: ty) => {
        impl<'a, S: Storage> PartialEq<$ty> for StrInner<S> {
            fn eq(&self, other: &$ty) -> bool {
                self.deref() == other.deref()
            }
        }

        impl<'a, S: Storage> PartialEq<StrInner<S>> for $ty {
            fn eq(&self, other: &StrInner<S>) -> bool {
                self.deref() == other.deref()
            }
        }

        impl<'a, S: Storage> PartialOrd<$ty> for StrInner<S> {
            fn partial_cmp(&self, other: &$ty) -> Option<Ordering> {
                Some(self.deref().cmp(other.deref()))
            }
        }

        impl<'a, S: Storage> PartialOrd<StrInner<S>> for $ty {
            fn partial_cmp(&self, other: &StrInner<S>) -> Option<Ordering> {
                Some(self.deref().cmp(other.deref()))
            }
        }
    };
}

c!(&'a str);
c!(&'a mut str);
c!(String);
c!(Box<str>);
c!(Cow<'a, str>);

impl<S: StorageMut> Write for StrInner<S> {
    fn write_str(&mut self, s: &str) -> FmtResult {
        self.push_str(s);
        Ok(())
    }
}

/// The [format] macro, but returning [Str].
///
/// # Examples
///
/// ```
/// use bytes_utils::{format_bytes, Str};
/// let s: Str = format_bytes!("Hello {}", "world");
/// assert_eq!("Hello world", s);
/// ```
#[macro_export]
macro_rules! format_bytes {
    ($($arg: tt)*) => {
        $crate::format_bytes_mut!($($arg)*).freeze()
    }
}

/// The [format] macro, but returning [StrMut].
///
/// # Examples
///
/// ```
/// use bytes_utils::{format_bytes_mut, StrMut};
/// let s: StrMut = format_bytes_mut!("Hello {}", "world");
/// assert_eq!("Hello world", s);
/// ```
#[macro_export]
macro_rules! format_bytes_mut {
    ($($arg: tt)*) => {{
        use std::fmt::Write;
        let mut buf = $crate::StrMut::default();
        write!(buf, $($arg)*).unwrap();
        buf
    }}
}

// TODO: Serde

pub type Str = StrInner<Bytes>;

impl Str {
    /// Extracts owned representation of the slice passed.
    ///
    /// This method accepts a string sub-slice of `self`. It then extracts the slice but as the
    /// [Str] type. This makes it easier to use "ordinary" string parsing/manipulation and then go
    /// back to holding the [Bytes]-based representation.
    ///
    /// This is zero-copy, the common part will be shared by reference counting.
    ///
    /// # Panics
    ///
    /// If the provided slice is not a sub-slice of `self`. This is checked based on address of the
    /// slice, not on the content.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use bytes_utils::Str;
    /// let owned = Str::from("Hello World");
    /// let borrowed_mid: &str = &owned[2..5];
    ///
    /// let mid: Str = owned.slice_ref(borrowed_mid);
    /// assert_eq!("Hello World", owned);
    /// assert_eq!("llo", mid);
    /// ```
    pub fn slice_ref(&self, subslice: &str) -> Self {
        let sub = self.0.slice_ref(subslice.as_bytes());
        Self(sub)
    }
}

pub type StrMut = StrInner<BytesMut>;

#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use proptest::prelude::*;

    use super::*;

    #[test]
    fn split_w_byte_index() {
        let v = Str::from("😈 ").split_whitespace_bytes().collect_vec();
        assert_eq!(1, v.len());
        assert_eq!("😈", v[0]);
    }

    #[test]
    fn split_same() {
        let v = Str::from("a").split_bytes("a").collect_vec();
        assert_eq!(2, v.len());
        assert_eq!("", v[0]);
        assert_eq!("", v[1]);
    }

    #[test]
    fn split_empty_pat() {
        let v = Str::from("a").split_bytes("").collect_vec();
        assert_eq!(3, v.len());
        assert_eq!("", v[0]);
        assert_eq!("a", v[1]);
        assert_eq!("", v[2]);
    }

    proptest! {
        #[test]
        fn split_whitespace(s: String) {
            let bstring = Str::from(&s);

            let bw = bstring.split_whitespace_bytes();
            let sw = s.split_whitespace();

            for (b, s) in bw.zip_eq(sw) {
                prop_assert_eq!(b, s);
            }
        }

        #[test]
        fn split_ascii_whitespace(s: String) {
            let bstring = Str::from(&s);

            let bw = bstring.split_ascii_whitespace_bytes();
            let sw = s.split_ascii_whitespace();

            for (b, s) in bw.zip_eq(sw) {
                prop_assert_eq!(b, s);
            }
        }

        #[test]
        fn lines(s: String) {
            let bstring = Str::from(&s);

            let bl = bstring.lines_bytes();
            let sl = s.lines();

            for (b, s) in bl.zip_eq(sl) {
                prop_assert_eq!(b, s);
            }
        }

        #[test]
        fn split(s: String, pat: String) {
            let bstring = Str::from(&s);

            let bs = bstring.split_bytes(&pat);
            let ss = s.split(&pat);

            for (b, s) in bs.zip_eq(ss) {
                prop_assert_eq!(b, s);
            }
        }

        #[test]
        fn split_n(s: String, pat: String, n in 0..5usize) {
            let bstring = Str::from(&s);

            let bs = bstring.splitn_bytes(n, &pat);
            let ss = s.splitn(n, &pat);

            for (b, s) in bs.zip_eq(ss) {
                prop_assert_eq!(b, s);
            }
        }

        #[test]
        fn rsplit(s: String, pat: String) {
            let bstring = Str::from(&s);

            let bs = bstring.rsplit_bytes(&pat);
            let ss = s.rsplit(&pat);

            for (b, s) in bs.zip_eq(ss) {
                prop_assert_eq!(b, s);
            }
        }

        #[test]
        fn rsplit_n(s: String, pat: String, n in 0..5usize) {
            let bstring = Str::from(&s);

            let bs = bstring.rsplitn_bytes(n, &pat);
            let ss = s.rsplitn(n, &pat);

            for (b, s) in bs.zip_eq(ss) {
                prop_assert_eq!(b, s);
            }
        }
    }
}
