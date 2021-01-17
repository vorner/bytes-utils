#![doc(test(attr(deny(warnings))))]
#![warn(missing_docs)]

//! # Extra utilities for the [bytes] crate.
//!
//! The [bytes] crate defines few traits and types to help with high-performance manipulation of
//! byte arrays. Nevertheless, it is more of an interface-level of library (many other crates
//! expose its types and traits in their own public interfaces) and therefore tries to be on the
//! lean side.
//!
//! One often wishes for some more auxiliary functionality „around“ these types and that's what
//! this crate aims to provide.
//!
//! ## The content
//!
//! * [SegmentedBuf] for concatenating multiple buffers into a large one without copying the bytes.

mod segmented;
pub mod string;

pub use segmented::SegmentedBuf;
pub use string::{Str, StrMut};
