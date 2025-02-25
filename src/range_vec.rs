//! Type wrappers to keep / lose track of the normalized status of
//! containers (vectors) and iterators of ranges.  A normalized
//! sequence of ranges is known to contain sorted and disjoint
//! non-empty ranges.
use alloc::vec::Vec;
use smallvec::SmallVec;

use crate::iterator_wrapper::NormalizedRangeIterWrapper;
use crate::Backing;
use crate::Endpoint;
use crate::NormalizedRangeIter;

/// A [`RangeVec<T>`] is a normalized [`SmallVec`] of `(T, T)`,
/// where the inline capacity is hardcoded to 2 ranges.
///
/// This branded wrapper around `SmallVec<[(T, T); 2]>` is the primary
/// representation for ranges at rest in this [`crate`].
///
/// [`SmallVec`]: https://docs.rs/smallvec/latest/smallvec/struct.SmallVec.html
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
#[repr(transparent)]
pub struct RangeVec<T: Endpoint> {
    inner: Backing<T>,
}

impl<T: Endpoint> RangeVec<T> {
    /// Returns an empty [`RangeVec`] (represents the empty set).
    #[inline(always)]
    pub fn new() -> Self {
        Self {
            inner: Backing::new(),
        }
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

    /// Returns an empty `RangeVec`.
    #[inline(always)]
    pub fn empty_set() -> Self {
        Default::default()
    }

    /// Returns a `RangeVec` that covers the whole universe of `T`s.
    #[inline(always)]
    pub fn universal_set() -> Self {
        Self::singleton((T::min_value(), T::max_value()))
    }

    /// Returns a `RangeVec` that represents the input `range` if it
    /// is a valid range (inclusing start endpoint less than or equal
    /// to the inclusive stop endpoint), and the empty set otherwise.
    ///
    /// This constructor may intrinsically return an empty set, so it
    /// accepts anything that may be converted to `Option<(T, T)>`,
    /// including ranges `(T, T)`.
    #[inline(always)]
    pub fn singleton(range: impl Into<Option<(T, T)>>) -> Self {
        fn doit<T: Endpoint>(maybe_range: Option<(T, T)>) -> RangeVec<T> {
            let mut inner = Backing::new();

            if let Some((lo, hi)) = maybe_range {
                if lo.cmp_end(hi) <= core::cmp::Ordering::Equal {
                    inner.push((lo, hi));
                }
            }

            unsafe { RangeVec::new_unchecked(inner) }
        }

        doit(range.into())
    }

    /// Normalizes this sequence of ranges into a fresh `RangeVec`.
    ///
    /// This operation takes \\(\mathcal{O}(n \log n)\\) time, where
    /// \\(n\\) is the number of ranges in the `ranges` argument.
    #[inline(always)]
    pub fn from(ranges: impl Into<crate::RangeCase<T>>) -> Self {
        crate::normalize_vec(ranges.into())
    }

    /// Converts `inner` to a normalized [`RangeVec`] in place.
    ///
    /// This operation is in-place and takes \\(\mathcal{O}(n \log n)\\)
    /// time.
    #[inline(always)]
    pub fn from_vec(inner: Vec<(T, T)>) -> Self {
        Self::from(inner)
    }

    /// Converts `inner` to a normalized [`RangeVec`] in place.
    ///
    /// This operation is in-place and takes \\(\mathcal{O}(n \log n)\\)
    /// time.
    #[inline(always)]
    pub fn from_smallvec<const N: usize>(inner: SmallVec<[(T, T); N]>) -> Self {
        Self::from(inner)
    }

    /// Returns a reference to the underlying ranges.
    #[inline(always)]
    pub fn inner(&self) -> &[(T, T)] {
        &self.inner
    }

    /// Extracts the underlying [`SmallVec`] of ranges.
    ///
    /// [`SmallVec`]: `smallvec::SmallVec`
    #[inline(always)]
    pub fn into_inner(self) -> Backing<T> {
        self.inner
    }

    /// Extracts the underlying vector of ranges.
    #[inline(always)]
    pub fn into_vec(self) -> Vec<(T, T)> {
        self.inner.into_vec()
    }

    /// Returns an iterator for the underlying normalized ranges.
    #[inline(always)]
    pub fn iter(
        &self,
    ) -> NormalizedRangeIterWrapper<core::iter::Copied<<&'_ Backing<T> as IntoIterator>::IntoIter>>
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
    #[inline(always)]
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
        NormalizedRangeIterWrapper<core::iter::Copied<<&'a Backing<T> as IntoIterator>::IntoIter>>;

    #[inline(always)]
    fn into_iter(self) -> Self::IntoIter {
        let iter = self.inner.iter().copied();
        unsafe { NormalizedRangeIterWrapper::new_unchecked(iter) }
    }
}

impl<T: Endpoint> core::ops::Deref for RangeVec<T> {
    type Target = [(T, T)];

    #[inline(always)]
    fn deref(&self) -> &[(T, T)] {
        <RangeVec<T>>::inner(self)
    }
}

#[cfg_attr(coverage_nightly, coverage(off))]
#[test]
fn test_smoke() {
    use smallvec::smallvec;

    assert_eq!(RangeVec::<u8>::new(), Default::default());
    assert_eq!(RangeVec::<u8>::new(), unsafe {
        RangeVec::new_unchecked(smallvec![])
    });
    assert!(RangeVec::<u8>::empty_set().is_empty());

    // Exercise a few other ways to generate the empty set
    assert_eq!(RangeVec::<u8>::singleton(None), RangeVec::empty_set());
    assert_eq!(RangeVec::<u8>::singleton((1u8, 0u8)), RangeVec::empty_set());
    assert_eq!(
        RangeVec::<u8>::singleton(Some((1u8, 0u8))),
        RangeVec::empty_set()
    );

    assert_eq!(
        RangeVec::<u8>::universal_set(),
        RangeVec::singleton((0u8, 255u8))
    );

    assert_eq!(
        RangeVec::<u8>::universal_set(),
        RangeVec::from([(0u8, 255u8)])
    );
    let ranges = unsafe { RangeVec::new_unchecked(smallvec![(2u8, 4u8), (10u8, 20u8)]) };

    assert_eq!(ranges[0], (2u8, 4u8));

    assert_eq!(&ranges, &ranges.iter().collect_range_vec());

    assert!(ranges.eqv(&ranges.iter().collect_range_vec()));
    assert!(!ranges.eqv(&Default::default()));
    assert!(!ranges.eqv(&unsafe { RangeVec::new_unchecked(smallvec![(2u8, 4u8), (11u8, 20u8)]) }));
    assert!(!ranges.eqv(&unsafe {
        RangeVec::new_unchecked(smallvec![(2u8, 4u8), (10u8, 20u8), (30u8, 30u8)])
    }));
    assert!(!ranges.eqv(&unsafe { RangeVec::new_unchecked(smallvec![(2u8, 4u8)]) }));

    assert_eq!(ranges.inner(), &ranges.iter().collect::<Vec<_>>());

    assert_eq!(ranges.inner(), &(&ranges).into_iter().collect::<Vec<_>>());
    assert_eq!(
        ranges.clone().into_vec(),
        ranges.into_iter().collect::<Vec<_>>()
    );
}
