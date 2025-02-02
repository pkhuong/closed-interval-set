//! Sometimes we don't care about whether data comes in normalized or
//! as arbitrary ranges.  This module defines traits and types to help
//! reduce the burden on callers in such cases.
use crate::Endpoint;
use crate::RangeVec;

/// Some functions don't care whether their input is normalized; they
/// take `impl Into<RangeCase<...>>`.
///
/// When a function doesn't care about normalisation *and* doesn't want
/// ownership, it can simply accept slices `&[(T, T)]`.
pub struct RangeCase<T: Endpoint> {
    inner: Vec<(T, T)>,
    normalized: bool,
}

impl<T: Endpoint> RangeCase<T> {
    /// Creates a [`RangeCase`] from a (not necessarily normalized) vector of ranges.
    #[inline(always)]
    pub fn from_vec(inner: Vec<(T, T)>) -> Self {
        Self {
            inner,
            normalized: false,
        }
    }

    /// Creates a [`RangeCase`] from a (normalized) [`RangeVec`]
    #[inline(always)]
    pub fn from_range_vec(set: RangeVec<T>) -> Self {
        Self {
            inner: set.into_inner(),
            normalized: true,
        }
    }

    /// Returns the underlying vector
    #[inline(always)]
    pub fn into_inner(self) -> Vec<(T, T)> {
        self.inner
    }

    /// Returns a [`RangeVec`] if the underlying vector is known to be
    /// normalized, and a [`Vec`] of ranges otherwise.
    #[inline(always)]
    pub fn unerase(self) -> Result<RangeVec<T>, Vec<(T, T)>> {
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

#[cfg_attr(coverage_nightly, coverage(off))]
#[test]
fn test_smoke() {
    let x: RangeCase<_> = vec![(1u8, 2u8)].into();
    assert_eq!(x.into_inner(), vec![(1u8, 2u8)]);

    let x: RangeCase<_> = vec![(1u8, 2u8)].into();
    assert_eq!(x.unerase().unwrap_err(), vec![(1u8, 2u8)]);

    let vec = unsafe { RangeVec::new_unchecked(vec![(1u8, 2u8)]) };
    let x: RangeCase<_> = vec.clone().into();
    assert_eq!(x.unerase().unwrap(), vec);
}
