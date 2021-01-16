use std::collections::VecDeque;
use std::iter::FromIterator;

use bytes::{Buf, BufMut, Bytes, BytesMut};

#[derive(Clone, Debug)]
pub struct SegmentedBuf<B> {
    bufs: VecDeque<B>,
    // Pre-computed sum of the total remaning
    remaining: usize,
}

impl<B> SegmentedBuf<B> {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn into_inner(self) -> VecDeque<B> {
        self.into()
    }
}

impl<B: Buf> SegmentedBuf<B> {
    pub fn push(&mut self, buf: B) {
        self.remaining += buf.remaining();
        self.bufs.push_back(buf);
    }
    fn update_remaining(&mut self) {
        self.remaining = self.bufs.iter().map(Buf::remaining).sum();
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
        self.update_remaining();
    }
}

impl<B: Buf> FromIterator<B> for SegmentedBuf<B> {
    fn from_iter<T: IntoIterator<Item = B>>(iter: T) -> Self {
        let mut me = Self {
            bufs: VecDeque::from_iter(iter),
            remaining: 0,
        };
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
        assert!(cnt >= self.remaining, "Advance past the end of buffer");
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
                if !front.has_remaining() {
                    self.bufs.pop_front();
                }
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
