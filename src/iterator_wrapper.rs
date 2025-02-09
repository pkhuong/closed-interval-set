//! Branded wrapper to mark iterators that yield normalized sequences
//! of ranges, i.e., that are known to contain sorted and fully disjoint
//! (not adjacent) non-empty ranges.
use std::iter::DoubleEndedIterator;
use std::iter::ExactSizeIterator;
use std::iter::Iterator;

use crate::ClosedRange;
use crate::NormalizedRangeIter;

/// This [`crate`] uses [`NormalizedRangeIterWrapper`] internally to
/// brand regular [`Iterator`]s that are known to yield normalized
/// ranges.  The wrapper itself is an [`Iterator`], and preserves
/// [`DoubleEndedIterator`] and [`ExactSizeIterator`] if the
/// underlying iterator implements them.
///
/// External users may rebrand iterators with this wrapper when they
/// are known to be normalized... but there are no guardrails here,
/// and getting this wrong will results in all sorts of broken outputs
/// (but not violate memory safety).
#[repr(transparent)]
pub struct NormalizedRangeIterWrapper<T: Iterator<Item: ClosedRange>>(T);

impl<T: Iterator<Item: ClosedRange>> NormalizedRangeIterWrapper<T> {
    /// Brands the iterator as normalized.  This is an unchecked promise!
    ///
    /// # Safety
    ///
    /// The caller must know that the iterator returns normalized ranges:
    /// non-empty ranges that are also sorted and fully disjoint.
    #[inline(always)]
    pub unsafe fn new_unchecked(inner: T) -> Self {
        Self(inner)
    }
}

impl<T: Iterator<Item: ClosedRange>> crate::private::Sealed for NormalizedRangeIterWrapper<T> {}

impl<T: Iterator<Item: ClosedRange>> NormalizedRangeIter for NormalizedRangeIterWrapper<T> {}

impl<T: Iterator<Item: ClosedRange>> Iterator for NormalizedRangeIterWrapper<T> {
    type Item = <T as Iterator>::Item;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<T: Iterator<Item: ClosedRange> + DoubleEndedIterator> DoubleEndedIterator
    for NormalizedRangeIterWrapper<T>
{
    #[inline(always)]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }
}

impl<T: Iterator<Item: ClosedRange> + ExactSizeIterator> ExactSizeIterator
    for NormalizedRangeIterWrapper<T>
{
}

#[cfg_attr(coverage_nightly, coverage(off))]
#[test]
fn test_iterator_forwarding() {
    let mut iter = unsafe {
        NormalizedRangeIterWrapper::new_unchecked(vec![(0u8, 1u8), (4u8, 10u8)].into_iter())
    };

    assert_eq!(iter.size_hint(), (2, Some(2)));
    assert_eq!(iter.next_back(), Some((4u8, 10u8)));
    assert_eq!(iter.next(), Some((0u8, 1u8)));
    assert_eq!(iter.next(), None);
}
