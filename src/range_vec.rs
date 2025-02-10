//! Type wrappers to keep / lose track of the normalized status of
//! containers (vectors) and iterators of ranges.  A normalized
//! sequence of ranges is known to contain sorted and disjoint
//! non-empty ranges.
use std::iter::DoubleEndedIterator;
use std::iter::ExactSizeIterator;

use crate::iterator_wrapper::NormalizedRangeIterWrapper;
use crate::Backing;
use crate::Endpoint;
use crate::NormalizedRangeIter;

/// A [`RangeVec<T>`] is a normalized [`Vec`] of `(T, T)`
///
/// This branded wrapper around `Vec<(T, T)>` is the primary
/// representation for ranges at rest in this [`crate`].
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
#[repr(transparent)]
pub struct RangeVec<T: Endpoint> {
    inner: Backing<T>,
}

impl<T: Endpoint> RangeVec<T> {
    /// Returns an empty [`RangeVec`] (represents the empty set).
    #[inline(always)]
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }

    /// Blindly tags a container as normalized: it contains valid
    /// (non-empty) closed ranges, the ranges don't overlap and aren't
    /// even adjacent, and the ranges are sorted in ascending order.
    ///
    /// This operation takes constant time in release mode, and linear
    /// time when debug assertions or internal checks are enabled.
    ///
    /// # Safety
    ///
    /// The caller must check that `inner` is normalized.
    #[inline(always)]
    pub unsafe fn new_unchecked(inner: Backing<T>) -> Self {
        #[cfg(any(feature = "internal_checks", debug_assertions))]
        assert!(crate::is_normalized(&inner[..]));
        Self { inner }
    }

    /// Converts `inner` to a normalized [`RangeVec`] in place.
    ///
    /// This operation is in-place and takes \\(\mathcal{O}(n \log n)\\)
    /// time.
    #[inline(always)]
    pub fn from_vec(inner: Vec<(T, T)>) -> Self {
        crate::normalize_vec(inner)
    }

    /// Returns a reference to the underlying ranges.
    #[inline(always)]
    pub fn inner(&self) -> &[(T, T)] {
        &self.inner
    }

    /// Extracts the underlying vector of ranges.
    #[inline(always)]
    pub fn into_inner(self) -> Backing<T> {
        self.inner
    }

    /// Returns an iterator for the underlying normalized ranges.
    #[inline(always)]
    pub fn iter(
        &self,
    ) -> impl '_ + NormalizedRangeIter<Item = (T, T)> + DoubleEndedIterator + ExactSizeIterator
    {
        let iter = self.inner.iter().copied();
        unsafe { NormalizedRangeIterWrapper::new_unchecked(iter) }
    }

    /// Determines whether these two [`RangeVec`]s represent the same
    /// ranges.
    ///
    /// This operation takes constant space and time linear in the
    /// shortest of the two inputs.
    pub fn eqv(&self, other: &RangeVec<T>) -> bool {
        self.iter().eqv(other.iter())
    }
}

impl<T: Endpoint> Default for RangeVec<T> {
    fn default() -> Self {
        RangeVec::new()
    }
}

impl<T: Endpoint> IntoIterator for RangeVec<T> {
    type Item = (T, T);
    type IntoIter = NormalizedRangeIterWrapper<<Backing<T> as IntoIterator>::IntoIter>;

    #[inline(always)]
    fn into_iter(self) -> Self::IntoIter {
        let iter = self.inner.into_iter();
        unsafe { NormalizedRangeIterWrapper::new_unchecked(iter) }
    }
}

impl<'a, T: Endpoint> IntoIterator for &'a RangeVec<T> {
    type Item = (T, T);
    type IntoIter =
        NormalizedRangeIterWrapper<std::iter::Copied<<&'a Backing<T> as IntoIterator>::IntoIter>>;

    #[inline(always)]
    fn into_iter(self) -> Self::IntoIter {
        let iter = self.inner.iter().copied();
        unsafe { NormalizedRangeIterWrapper::new_unchecked(iter) }
    }
}

impl<T: Endpoint> std::ops::Deref for RangeVec<T> {
    type Target = [(T, T)];

    #[inline(always)]
    fn deref(&self) -> &[(T, T)] {
        <RangeVec<T>>::inner(self)
    }
}

#[cfg_attr(coverage_nightly, coverage(off))]
#[test]
fn test_smoke() {
    assert_eq!(RangeVec::<u8>::new(), Default::default());
    assert_eq!(RangeVec::<u8>::new(), unsafe {
        RangeVec::new_unchecked(vec![])
    });
    assert!(RangeVec::<u8>::new().is_empty());

    let ranges = unsafe { RangeVec::new_unchecked(vec![(2u8, 4u8), (10u8, 20u8)]) };

    assert_eq!(ranges[0], (2u8, 4u8));

    assert_eq!(&ranges, &ranges.iter().collect_range_vec());

    assert!(ranges.eqv(&ranges.iter().collect_range_vec()));
    assert!(!ranges.eqv(&Default::default()));
    assert!(!ranges.eqv(&unsafe { RangeVec::new_unchecked(vec![(2u8, 4u8), (11u8, 20u8)]) }));
    assert!(!ranges
        .eqv(&unsafe { RangeVec::new_unchecked(vec![(2u8, 4u8), (10u8, 20u8), (30u8, 30u8)]) }));
    assert!(!ranges.eqv(&unsafe { RangeVec::new_unchecked(vec![(2u8, 4u8)]) }));

    assert_eq!(ranges.inner(), &ranges.iter().collect::<Vec<_>>());

    assert_eq!(ranges.inner(), &(&ranges).into_iter().collect::<Vec<_>>());
    assert_eq!(
        ranges.clone().into_inner(),
        ranges.into_iter().collect::<Vec<_>>()
    );
}
