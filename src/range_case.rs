//! Sometimes we don't care about whether data comes in normalized or
//! as arbitrary ranges.  This module defines traits and types to help
//! reduce the burden on callers in such cases.
use alloc::vec::Vec;
use smallvec::SmallVec;

use crate::Backing;
use crate::ClosedRange;
use crate::Endpoint;
use crate::RangeVec;

/// Some functions don't care whether their input is normalized; they
/// take `impl Into<RangeCase<...>>`.
///
/// When a function doesn't care about normalisation *and* doesn't want
/// ownership, it can simply accept slices `&[(T, T)]`.
#[derive(Clone, Debug)]
pub struct RangeCase<T: Endpoint> {
    inner: Backing<T>,
    normalized: bool,
}

impl<T: Endpoint> RangeCase<T> {
    /// Creates a [`RangeCase`] from a (not necessarily normalized) vector of ranges.
    ///
    /// This operation takes constant time.
    #[inline(always)]
    pub fn from_vec(inner: Vec<(T, T)>) -> Self {
        Self {
            inner: inner.into(),
            normalized: false,
        }
    }

    /// Creates a [`RangeCase`] from a (not necessarily normalized) smallvec of ranges.
    ///
    /// This operation takes constant time.
    pub fn from_smallvec<const N: usize>(inner: SmallVec<[(T, T); N]>) -> Self {
        // `INLINE_SIZE == 0` unless inline storage is enabled.
        #[cfg_attr(
            not(feature = "inline_storage"),
            allow(clippy::absurd_extreme_comparisons)
        )]
        let inner: Backing<T> = if inner.len() <= crate::INLINE_SIZE {
            inner.into_iter().collect()
        } else {
            inner.into_vec().into()
        };

        Self {
            inner,
            normalized: false,
        }
    }

    /// Creates a [`RangeCase`] from a (not necessarily normalized) slice of ranges.
    ///
    /// This operation takes time linear in the length of the slice.
    pub fn from_slice(slice: impl AsRef<[(T, T)]>) -> Self {
        Self::from_smallvec::<{ crate::INLINE_SIZE }>(SmallVec::from_slice(slice.as_ref()))
    }

    /// Creates a [`RangeCase`] from a (normalized) [`RangeVec`]
    ///
    /// This operation takes constant time.
    #[inline(always)]
    pub fn from_range_vec(set: RangeVec<T>) -> Self {
        Self {
            inner: set.into_inner(),
            normalized: true,
        }
    }

    /// Returns the underlying vector
    ///
    /// This operation takes constant time.
    #[inline(always)]
    pub fn into_inner(self) -> Backing<T> {
        self.inner
    }

    /// Returns a [`RangeVec`] if the underlying vector is known to be
    /// normalized, and a [`Vec`] of ranges otherwise.
    ///
    /// This operation takes constant time.
    #[inline(always)]
    pub fn unerase(self) -> Result<RangeVec<T>, Backing<T>> {
        if self.normalized {
            Ok(unsafe { RangeVec::new_unchecked(self.inner) })
        } else {
            Err(self.inner)
        }
    }
}

impl<T: Endpoint> From<RangeVec<T>> for RangeCase<T> {
    #[inline(always)]
    fn from(item: RangeVec<T>) -> RangeCase<T> {
        RangeCase::from_range_vec(item)
    }
}

impl<T: Endpoint> From<Vec<(T, T)>> for RangeCase<T> {
    #[inline(always)]
    fn from(item: Vec<(T, T)>) -> RangeCase<T> {
        RangeCase::from_vec(item)
    }
}

impl<T: Endpoint, const N: usize> From<SmallVec<[(T, T); N]>> for RangeCase<T> {
    #[inline(always)]
    fn from(item: SmallVec<[(T, T); N]>) -> RangeCase<T> {
        RangeCase::from_smallvec(item)
    }
}

impl<T: Endpoint> From<&[(T, T)]> for RangeCase<T> {
    #[inline(always)]
    fn from(item: &[(T, T)]) -> RangeCase<T> {
        RangeCase::from_slice(item)
    }
}

impl<T: Endpoint, const N: usize> From<&[(T, T); N]> for RangeCase<T> {
    #[inline(always)]
    fn from(item: &[(T, T); N]) -> RangeCase<T> {
        RangeCase::from_slice(item)
    }
}

impl<T: Endpoint, const N: usize> From<[(T, T); N]> for RangeCase<T> {
    #[inline(always)]
    fn from(item: [(T, T); N]) -> RangeCase<T> {
        RangeCase::from_slice(item)
    }
}

impl<T: Endpoint> From<(T, T)> for RangeCase<T> {
    #[inline(always)]
    fn from(item: (T, T)) -> RangeCase<T> {
        RangeCase::from_slice([item])
    }
}

impl<T: Endpoint> From<Option<(T, T)>> for RangeCase<T> {
    #[inline(always)]
    fn from(item: Option<(T, T)>) -> RangeCase<T> {
        RangeCase::from_slice(item.as_slice())
    }
}

impl<T: Endpoint, Item> core::iter::FromIterator<Item> for RangeCase<T>
where
    Item: ClosedRange<EndT = T>,
{
    fn from_iter<It: IntoIterator<Item = Item>>(iter: It) -> Self {
        Self::from_smallvec::<{ crate::INLINE_SIZE }>(iter.into_iter().map(|x| x.get()).collect())
    }
}

#[cfg_attr(coverage_nightly, coverage(off))]
#[test]
fn test_smoke() {
    use alloc::vec;
    use smallvec::smallvec;

    {
        let empty_1: RangeCase<u8> = RangeCase::from_slice([]);
        let empty_2: RangeCase<_> = None.into();
        assert_eq!(empty_1.into_inner(), empty_2.into_inner());
    }

    let x: RangeCase<_> = vec![(1u8, 2u8)].into();
    assert_eq!(x.clone().into_inner().into_vec(), vec![(1u8, 2u8)]);

    // Test other 1-item conversions
    {
        let y: RangeCase<_> = (1u8, 2u8).into();
        assert_eq!(x.clone().into_inner(), y.into_inner());

        let y: RangeCase<_> = Some((1u8, 2u8)).into();
        assert_eq!(x.clone().into_inner(), y.into_inner());
    }

    {
        let x: RangeCase<_> = (&[(1u8, 2u8), (3u8, 4u8), (10u8, 255u8)][..]).into();
        assert_eq!(
            x.into_inner().into_vec(),
            vec![(1u8, 2u8), (3u8, 4u8), (10u8, 255u8)]
        );

        let x: RangeCase<_> = [(1u8, 2u8)].into();
        assert_eq!(x.into_inner().into_vec(), vec![(1u8, 2u8)]);

        let x: RangeCase<_> = (&[(1u8, 2u8)]).into();
        assert_eq!(x.into_inner().into_vec(), vec![(1u8, 2u8)]);
    }

    {
        let smallvec: Backing<u8> = smallvec![(1u8, 2u8)];
        let x: RangeCase<_> = smallvec.into();
        assert_eq!(x.unerase().unwrap_err().into_vec(), vec![(1u8, 2u8)]);

        let smallvec: Backing<u8> = smallvec![(1u8, 2u8), (10u8, 12u8), (20u8, 30u8)];
        let x: RangeCase<_> = smallvec.into();
        assert_eq!(
            x.unerase().unwrap_err().into_vec(),
            vec![(1u8, 2u8), (10u8, 12u8), (20u8, 30u8)]
        );
    }

    {
        let smallervec: SmallVec<[(u8, u8); 0]> = smallvec![(1u8, 2u8)];
        let x: RangeCase<_> = smallervec.into();
        assert_eq!(x.unerase().unwrap_err().into_vec(), vec![(1u8, 2u8)]);

        let smallervec: SmallVec<[(u8, u8); 0]> = smallvec![(1u8, 2u8), (3u8, 4u8), (10u8, 11u8)];
        let x: RangeCase<_> = smallervec.into();
        assert_eq!(
            x.unerase().unwrap_err().into_vec(),
            vec![(1u8, 2u8), (3u8, 4u8), (10u8, 11u8)]
        );
    }

    {
        let largervec: SmallVec<[(u8, u8); crate::INLINE_SIZE + 1]> = smallvec![(1u8, 2u8)];
        let x: RangeCase<_> = largervec.into();
        assert_eq!(x.unerase().unwrap_err().into_vec(), vec![(1u8, 2u8)]);

        let largervec: SmallVec<[(u8, u8); crate::INLINE_SIZE + 1]> =
            smallvec![(1u8, 2u8), (3u8, 4u8), (10u8, 11u8)];
        let x: RangeCase<_> = largervec.into();
        assert_eq!(
            x.unerase().unwrap_err().into_vec(),
            vec![(1u8, 2u8), (3u8, 4u8), (10u8, 11u8)]
        );
    }

    let itcase: RangeCase<u8> = RangeCase::from_iter(&[(1u8, 2u8)]);
    assert_eq!(itcase.unerase().unwrap_err().into_vec(), vec![(1u8, 2u8)]);

    let vec = unsafe { RangeVec::new_unchecked(smallvec![(1u8, 2u8)]) };
    let x: RangeCase<_> = vec.clone().into();
    assert_eq!(x.unerase().unwrap(), vec);
}
