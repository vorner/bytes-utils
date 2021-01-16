use std::collections::VecDeque;
use std::iter::FromIterator;

use bytes::{Buf, BufMut, Bytes, BytesMut};

/// A concatenation of multiple buffers into a large one, without copying the bytes over.
///
/// Note that this doesn't provide a continuous slice view into them, it is split into the segments
/// of the original smaller buffers.
///
/// # Why
///
/// This can be used, for example, if data of unknown length is coming over the network (for
/// example, the bodies in [hyper] act a bit like this, it returns a stream of [Bytes] buffers).
/// One might want to accumulate the whole body before acting on it, possibly by parsing it through
/// [serde] or [prost]. Options would include:
///
/// * Have a `Vec<u8>` and extend it with each chunk. This needlessly copy the bytes every time and
///   reallocates if the vector grows too large.
/// * Repeatedly use [chain][Buf::chain], but this changes the type of the whole buffer, therefore
///   needs to be boxed.
/// * Use [hyper::body::aggregate] to create a [Buf] implementation that concatenates all of them
///   together, but lacks any kind of flexibility (like protecting against loading too much data
///   into memory).
///
/// This type allows for concatenating multiple buffers, either all at once, or by incrementally
/// pushing more buffers to the end.
///
/// # Heterogeneous buffers
///
/// This expects all the buffers are of the same type. If different-typed buffers are needed, one
/// needs to use dynamic dispatch, either something like `SegmentedBuf<Box<Buf>>` or
/// `SegmentedBuf<&mut Buf>`.
///
/// # Example
///
/// ```rust
/// # use std::io::Read;
/// # use bytes::{Bytes, Buf};
/// # use bytes_utils::SegmentedBuf;
/// let mut buf = SegmentedBuf::new();
/// buf.push(Bytes::from("Hello"));
/// buf.push(Bytes::from(" "));
/// buf.push(Bytes::from("World"));
///
/// assert_eq!(3, buf.segments());
/// assert_eq!(11, buf.remaining());
/// assert_eq!(b"Hello", buf.chunk());
///
/// let mut out = String::new();
/// buf.reader().read_to_string(&mut out).expect("Doesn't cause IO errors");
/// assert_eq!("Hello World", out);
/// ```
///
/// # FIFO behaviour
///
/// The buffers are dropped once their data are completely consumed. Additionally, it is possible
/// to add more buffers to the end, even while some of the previous buffers were partially or fully
/// consumed. That makes it usable as kind of a queue (that operates on the buffers, not individual
/// bytes).
///
/// ```rust
/// # use bytes::{Bytes, Buf};
/// # use bytes_utils::SegmentedBuf;
/// let mut buf = SegmentedBuf::new();
/// buf.push(Bytes::from("Hello"));
/// assert_eq!(1, buf.segments());
///
/// let mut out = [0; 3];
/// buf.copy_to_slice(&mut out);
/// assert_eq!(&out, b"Hel");
/// assert_eq!(2, buf.remaining());
/// assert_eq!(1, buf.segments());
///
/// buf.push(Bytes::from("World"));
/// assert_eq!(7, buf.remaining());
/// assert_eq!(2, buf.segments());
///
/// buf.copy_to_slice(&mut out);
/// assert_eq!(&out, b"loW");
/// assert_eq!(4, buf.remaining());
/// assert_eq!(1, buf.segments());
/// ```
///
/// [hyper]: https://docs.rs/hyper
/// [serde]: https://docs.rs/serde
/// [prost]: https://docs.rs/prost
/// [hyper::body::aggregate]: https://docs.rs/hyper/0.14.2/hyper/body/fn.aggregate.html
#[derive(Clone, Debug)]
pub struct SegmentedBuf<B> {
    bufs: VecDeque<B>,
    // Pre-computed sum of the total remaning
    remaining: usize,
}

impl<B> SegmentedBuf<B> {
    /// Creates a new empty instance.
    ///
    /// The instance can be [pushed][SegmentedBuf::push] or [extended][Extend] later.
    ///
    /// Alternatively, one may create it directly from an iterator, a [Vec] or a [VecDeque] of
    /// buffers.
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the yet unconsumed sequence of buffers.
    pub fn into_inner(self) -> VecDeque<B> {
        self.into()
    }

    /// Returns the number of segments (buffers) this contains.
    pub fn segments(&self) -> usize {
        self.bufs.len()
    }
}

impl<B: Buf> SegmentedBuf<B> {
    /// Extends the buffer by another segment.
    ///
    /// The newly added segment is added to the end of the buffer (the buffer works as a FIFO).
    pub fn push(&mut self, buf: B) {
        self.remaining += buf.remaining();
        self.bufs.push_back(buf);
        self.clean_empty();
    }
    fn update_remaining(&mut self) {
        self.remaining = self.bufs.iter().map(Buf::remaining).sum();
    }
    fn clean_empty(&mut self) {
        loop {
            match self.bufs.front() {
                Some(b) if !b.has_remaining() => {
                    self.bufs.pop_front();
                }
                _ => break,
            }
        }
    }
}

impl<B> Default for SegmentedBuf<B> {
    fn default() -> Self {
        Self {
            bufs: VecDeque::new(),
            remaining: 0,
        }
    }
}

impl<B: Buf> From<Vec<B>> for SegmentedBuf<B> {
    fn from(bufs: Vec<B>) -> Self {
        Self::from(VecDeque::from(bufs))
    }
}

impl<B: Buf> From<VecDeque<B>> for SegmentedBuf<B> {
    fn from(bufs: VecDeque<B>) -> Self {
        let mut me = Self { bufs, remaining: 0 };
        me.clean_empty();
        me.update_remaining();
        me
    }
}

impl<B> From<SegmentedBuf<B>> for VecDeque<B> {
    fn from(me: SegmentedBuf<B>) -> Self {
        me.bufs
    }
}

impl<B: Buf> Extend<B> for SegmentedBuf<B> {
    fn extend<T: IntoIterator<Item = B>>(&mut self, iter: T) {
        self.bufs.extend(iter);
        self.clean_empty();
        self.update_remaining();
    }
}

impl<B: Buf> FromIterator<B> for SegmentedBuf<B> {
    fn from_iter<T: IntoIterator<Item = B>>(iter: T) -> Self {
        let mut me = Self {
            bufs: VecDeque::from_iter(iter),
            remaining: 0,
        };
        me.clean_empty();
        me.update_remaining();
        me
    }
}

impl<B: Buf> Buf for SegmentedBuf<B> {
    fn remaining(&self) -> usize {
        self.remaining
    }

    fn chunk(&self) -> &[u8] {
        self.bufs.front().map(Buf::chunk).unwrap_or_default()
    }

    fn advance(&mut self, mut cnt: usize) {
        assert!(cnt <= self.remaining, "Advance past the end of buffer");
        self.remaining -= cnt;
        while cnt > 0 {
            let front = self
                .bufs
                .front_mut()
                .expect("Missing buffers to provide remaining");
            let front_remaining = front.remaining();
            if front_remaining >= cnt {
                front.advance(cnt);
                break;
            } else {
                // We advance past the whole front buffer
                cnt -= front_remaining;
                self.bufs.pop_front();
            }
        }
        self.clean_empty();
    }

    fn copy_to_bytes(&mut self, len: usize) -> Bytes {
        assert!(len <= self.remaining(), "`len` greater than remaining");
        match self.bufs.front_mut() {
            // Special optimized case. The whole request comes from the front buffer. That one may
            // be optimized to do something more efficient, like slice the Bytes (if B == Bytes)
            // instead of copying, so we take the opportunity if it offers itself.
            Some(front) if front.remaining() >= len => {
                self.remaining -= len;
                let res = front.copy_to_bytes(len);
                self.clean_empty();
                res
            }
            // The general case, borrowed from the default implementation (there's no way to
            // delegate to it, is there?)
            _ => {
                let mut res = BytesMut::with_capacity(len);
                res.put(self.take(len));
                res.freeze()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::cmp;
    use std::io::Read;

    use proptest::prelude::*;

    use super::*;

    #[test]
    fn empty() {
        let mut b = SegmentedBuf::<Bytes>::new();

        assert!(!b.has_remaining());
        assert_eq!(0, b.remaining());
        assert!(b.chunk().is_empty());
        assert_eq!(0, b.segments());

        b.copy_to_slice(&mut []);
        b.advance(0);
        assert_eq!(0, b.reader().read(&mut [0; 10]).unwrap());
    }

    fn segmented() -> SegmentedBuf<Bytes> {
        vec![
            Bytes::from("Hello"),
            Bytes::from(" "),
            Bytes::new(),
            Bytes::from("World"),
        ]
        .into()
    }

    #[test]
    fn segments() {
        let mut b = segmented();
        assert_eq!(11, b.remaining());
        assert_eq!(b"Hello", b.chunk());
        assert_eq!(4, b.segments());
        b.advance(3);
        assert_eq!(8, b.remaining());
        assert_eq!(b"lo", b.chunk());
        assert_eq!(4, b.segments());
    }

    #[test]
    fn to_bytes_all() {
        let mut b = segmented();
        let bytes = b.copy_to_bytes(11);
        assert_eq!("Hello World", &bytes);
    }

    #[test]
    fn advance_within() {
        let mut b = segmented();
        b.advance(2);
        assert_eq!(4, b.segments());
        assert_eq!(9, b.remaining());
        assert_eq!(b"llo", b.chunk());
    }

    #[test]
    fn advance_border() {
        let mut b = segmented();
        b.advance(5);
        assert_eq!(3, b.segments());
        assert_eq!(6, b.remaining());
        assert_eq!(b" ", b.chunk());
    }

    #[test]
    fn advance_across() {
        let mut b = segmented();
        b.advance(7);
        assert_eq!(1, b.segments());
        assert_eq!(4, b.remaining());
        assert_eq!(b"orld", b.chunk());
    }

    #[test]
    fn empty_at_border() {
        let mut b = segmented();
        b.advance(6);
        assert_eq!(1, b.segments());
        assert_eq!(5, b.remaining());
        assert_eq!(b"World", b.chunk());
    }

    #[test]
    fn empty_bufs() {
        fn is_empty(b: &SegmentedBuf<Bytes>) {
            assert_eq!(0, b.segments());
            assert_eq!(0, b.remaining());
            assert_eq!(b"", b.chunk());
        }

        is_empty(&vec![].into());
        is_empty(&vec![Bytes::new(), Bytes::new()].into());
        is_empty(&vec![Bytes::new(), Bytes::new()].into_iter().collect());

        let mut b = SegmentedBuf::new();
        is_empty(&b);
        b.push(Bytes::new());
        is_empty(&b);
        b.extend(vec![Bytes::new(), Bytes::new()]);
        is_empty(&b);
    }

    proptest! {
        #[test]
        fn random(bufs: Vec<Vec<u8>>, splits in proptest::collection::vec(0..10usize, 1..10)) {
            let concat: Vec<u8> = bufs.iter().flat_map(|b| b.iter()).copied().collect();
            let mut segmented = bufs.iter()
                .map(|b| &b[..])
                .collect::<SegmentedBuf<_>>();
            assert_eq!(concat.len(), segmented.remaining());
            assert!(segmented.segments() <= bufs.len());
            assert!(concat.starts_with(segmented.chunk()));
            let mut bytes = segmented.clone().copy_to_bytes(segmented.remaining());
            assert_eq!(&concat[..], &bytes[..]);

            let mut fifo = SegmentedBuf::new();
            let mut buf_pos = bufs.iter();

            for split in splits {
                if !bytes.has_remaining() {
                    break;
                }
                let split = cmp::min(bytes.remaining(), split);
                while fifo.remaining() < split {
                    fifo.push(&buf_pos.next().unwrap()[..]);
                }
                let c1 = bytes.copy_to_bytes(split);
                let c2 = segmented.copy_to_bytes(split);
                assert_eq!(c1, c2);
                assert_eq!(bytes.remaining(), segmented.remaining());
            }
        }
    }
}
