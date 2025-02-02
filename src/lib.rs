//! The `closed_interval_set` crate manipulates unions of closed
//! intervals that are physically represented as containers of pairs
//! of endpoints.
#![deny(missing_docs)]
// https://github.com/taiki-e/cargo-llvm-cov?tab=readme-ov-file#exclude-code-from-coverage
#![cfg_attr(coverage_nightly, feature(coverage_attribute))]

mod complement;
mod intersection;
pub mod iterator_wrapper;
mod normalize;
mod primitive_endpoint;
mod range_case;
mod range_vec;
mod slice_sequence;
mod union;

pub use range_case::RangeCase;
pub use range_vec::RangeVec;

pub use normalize::is_normalized;
pub use normalize::normalize_vec;

pub use complement::complement_vec;
pub use intersection::intersect_vec;
pub use union::union_vec;

/// An [`Endpoint`] is the left or right limit of a closed interval
/// `[left, right]`.
///
/// [`Endpoint`] types must have maximum and minimum values.  For
/// bounded integer types, that's simply `T::MIN` or `T::MAX`;
/// in general, types may have to be extended, just like floating
/// point values have +/- infinity.
///
/// [`Endpoint`] types must also be enumerable in both ascending and
/// descending order.
///
/// There is an implementation for all 10 primitive fixed-width
/// integer types (signed/unsigned 8, 16, 32, 64, and 128 bits),
/// and for [`isize`] and [`usize`].
pub trait Endpoint: Copy + Ord {
    /// The minimum value for values of type [`Endpoint`]:
    ///
    /// \\[ \forall x : \mathtt{Self}, x \geq \mathtt{Self::min\\_value}() \\]
    fn min_value() -> Self;

    /// The maximum value for values of type [`Endpoint`]:
    ///
    /// \\[ \forall x : \mathtt{Self}, x \leq \mathtt{Self::max\\_value}() \\]
    fn max_value() -> Self;

    /// Returns the minimum [`Endpoint`] value strictly
    /// greater than `self`, or `None` if there is no
    /// such value (iff `self == Self::max_value()`).
    ///
    /// \\[ \forall \mathtt{self}, x: \mathtt{Self}, x > \mathtt{self} \Rightarrow x \geq \mathtt{self.next\\_after}() \\]
    #[inline(always)]
    fn next_after(self) -> Option<Self> {
        self.increase_toward(Self::max_value())
    }

    /// Returns the maximum [`Endpoint`] value strictly
    /// less than `self`, or `None` if there is no
    /// such value (iff `self == Self::min_value()`).
    ///
    /// \\[ \forall \mathtt{self}, x: \mathtt{Self}, x < \mathtt{self} \Rightarrow x \leq \mathtt{self.prev\\_before}() \\]
    #[inline(always)]
    fn prev_before(self) -> Option<Self> {
        self.decrease_toward(Self::min_value())
    }

    /// Returns [`prev_before()`] iff `other < self`, and [`None`]
    /// otherwise.
    ///
    /// In practice, it's usually easier to directly implement this
    /// method instead of [`prev_before()`] (`other < self` guarantees
    /// there is a previous value for `self`), so [`prev_before()`] is
    /// implemented in terms of [`Self::decrease_toward()`].
    ///
    /// [`prev_before()`]: `Self::prev_before`
    fn decrease_toward(self, other: Self) -> Option<Self>;

    /// Returns [`next_after()`] iff `other > self`, and [`None`]
    /// otherwise.
    ///
    /// In practice, it's usually easier to directly implement this
    /// method instead of [`next_after()`] (`other > self` guarantees
    /// there is a next value for `self`), so [`next_after()`] is
    /// implemented in terms of [`Self::increase_toward()`].
    ///
    /// [`next_after()`]: `Self::next_after`
    fn increase_toward(self, other: Self) -> Option<Self>;
}

/// We represent closed ranges as pairs of [`Endpoint`]s.
type Pair<T> = (T, T);

mod private {
    pub trait Sealed {}
}

/// A [`ClosedRange`] represents a closed range of values with pairs
/// of [`Endpoint`]s.
///
/// This trait stands for `(T, T)` `&(T, T)`, where `T` implements
/// [`Endpoint`].
///
/// The [`ClosedRange`] trait is sealed and cannot be implemented for
/// types outside this crate.  External code *may* have to write down
/// the trait's name, but most likely shouldn't try to actually invoke
/// any method on that trait.
pub trait ClosedRange: Copy + Ord + private::Sealed {
    /// The type of the endpoints for this range.
    #[doc(hidden)]
    type EndT: Endpoint;

    /// Returns a copy of the range represented by this
    /// [`ClosedRange`] instance.
    #[doc(hidden)]
    fn get(self) -> Pair<Self::EndT>;
}

/// A [`NormalizedRangeIter`] yields a sorted sequence of
/// non-overlapping, non-adjacent, non-empty closed ranges.
///
/// It's hard to check for this property at runtime, so this
/// trait is sealed.
pub trait NormalizedRangeIter: private::Sealed + Sized + Iterator<Item: ClosedRange> {
    /// Determines whether this range iterator is equivalent to
    /// (represents the same set of values as) another.
    fn eqv(
        mut self,
        other: impl IntoNormalizedRangeIter<
            IntoIter: Iterator<Item: ClosedRange<EndT = <Self::Item as ClosedRange>::EndT>>,
        >,
    ) -> bool {
        let mut other = other.into_iter();
        loop {
            match (self.next(), other.next()) {
                (Some(a), Some(b)) => {
                    if a.get() != b.get() {
                        return false;
                    }
                }
                (None, None) => return true,
                _ => return false,
            }
        }
    }

    /// Returns an iterator for the complement of this normalized range iterator.
    ///
    /// The result is also a [`NormalizedRangeIter`].
    #[inline(always)]
    fn complement(self) -> complement::ComplementIterator<Self> {
        complement::ComplementIterator::new(self)
    }

    /// Returns an iterator for the intersection of this normalized range iterator
    /// and another [`RangeVec`] of normalized ranges.
    ///
    /// The result is also a [`NormalizedRangeIter`].
    #[inline(always)]
    fn intersect_vec<'a>(
        self,
        other: &'a RangeVec<<Self::Item as ClosedRange>::EndT>,
    ) -> impl 'a + NormalizedRangeIter<Item = Pair<<Self::Item as ClosedRange>::EndT>>
    where
        Self: 'a,
    {
        // Unsafe because the interface assumes both arguments are normalized.
        unsafe { crate::intersection::intersect(self, other) }
    }

    /// Collects the contents of a [`NormalizedRangeIter`] into a [`RangeVec`]
    fn collect_range_vec(self) -> RangeVec<<Self::Item as ClosedRange>::EndT> {
        let inner: Vec<_> = self.map(|range| range.get()).collect();
        unsafe { RangeVec::new_unchecked(inner) }
    }
}

/// A [`IntoNormalizedRangeIter`] is an [`IntoIterator`] that turns
/// into an [`NormalizedRangeIter`].
pub trait IntoNormalizedRangeIter: IntoIterator<IntoIter: NormalizedRangeIter> {}

impl<T: IntoIterator<IntoIter: NormalizedRangeIter>> IntoNormalizedRangeIter for T {}

impl<T: Endpoint> private::Sealed for (T, T) {}

impl<T: Endpoint> ClosedRange for (T, T) {
    type EndT = T;

    #[inline(always)]
    fn get(self) -> (T, T) {
        self
    }
}

impl<T: Endpoint> private::Sealed for &(T, T) {}

impl<T: Endpoint> ClosedRange for &(T, T) {
    type EndT = T;

    #[inline(always)]
    fn get(self) -> (T, T) {
        *self
    }
}

/// The return type of `ClosedRange::get()`.
type ClosedRangeVal<T> = Pair<<T as ClosedRange>::EndT>;

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
fn ranges_to_bits(ranges: &[(u8, u8)]) -> Vec<bool> {
    let mut marks = vec![false; 256];

    for (start, stop) in ranges.iter().copied() {
        if start <= stop {
            for i in start..=stop {
                marks[i as usize] = true;
            }
        }
    }

    marks
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod test {
    use super::*;

    #[test]
    fn test_min_max() {
        assert_eq!(<u8 as Endpoint>::min_value(), 0);
        assert_eq!(<u8 as Endpoint>::max_value(), 255);

        assert_eq!(<i8 as Endpoint>::min_value(), -128);
        assert_eq!(<i8 as Endpoint>::max_value(), 127);

        assert_eq!(<i32 as Endpoint>::min_value(), i32::MIN);
        assert_eq!(<i32 as Endpoint>::max_value(), i32::MAX);

        assert_eq!(<isize as Endpoint>::min_value(), isize::MIN);
        assert_eq!(<isize as Endpoint>::max_value(), isize::MAX);

        assert_eq!(<usize as Endpoint>::min_value(), usize::MIN);
        assert_eq!(<usize as Endpoint>::max_value(), usize::MAX);
    }

    #[test]
    fn test_prev_next_u64() {
        assert_eq!(0u64.prev_before(), None);
        assert_eq!(0u64.next_after(), Some(1));

        assert_eq!(u64::MAX.prev_before(), Some(u64::MAX - 1));
        assert_eq!(u64::MAX.next_after(), None);

        assert_eq!(0u64.decrease_toward(0u64), None);
        assert_eq!(0u64.increase_toward(10u64), Some(1));

        assert_eq!(1u64.decrease_toward(0u64), Some(0u64));
        assert_eq!(1u64.decrease_toward(1u64), None);
        assert_eq!(1u64.decrease_toward(2u64), None);

        assert_eq!(1u64.increase_toward(0u64), None);
        assert_eq!(1u64.increase_toward(1u64), None);
        assert_eq!(1u64.increase_toward(2u64), Some(2u64));

        assert_eq!(u64::MAX.increase_toward(u64::MAX), None);
        assert_eq!(u64::MAX.decrease_toward(0), Some(u64::MAX - 1));
    }

    #[test]
    fn test_closed_range() {
        let ranges = vec![(1u8, 2u8), (10u8, 4u8)];

        assert_eq!(
            &ranges.iter().map(ClosedRange::get).collect::<Vec<_>>(),
            &ranges
        );
        assert_eq!(
            ranges
                .clone()
                .into_iter()
                .map(ClosedRange::get)
                .collect::<Vec<_>>(),
            ranges
        );
    }

    proptest::proptest! {
        #[test]
        fn test_increase(x: u8) {
            assert_eq!(<u8 as Endpoint>::max_value(), u8::MAX);

            if x != u8::MAX {
                assert_eq!(x.next_after(), Some(x + 1));
            } else {
                assert_eq!(x.next_after(), None);
            }
        }

        #[test]
        fn test_decrease(x: u8) {
            assert_eq!(<u8 as Endpoint>::min_value(), 0u8);

            if x != 0u8 {
                assert_eq!(x.prev_before(), Some(x - 1));
            } else {
                assert_eq!(x.prev_before(), None);
            }
        }

        #[test]
        fn test_toward(x: u8, y: u8) {
            let (x, y) = (x.min(y), x.max(y));

            assert_eq!(x.decrease_toward(y), None);
            assert_eq!(y.increase_toward(x), None);

            if x == y {
                assert_eq!(x.increase_toward(y), None);
                assert_eq!(x.decrease_toward(y), None);
                assert_eq!(y.increase_toward(x), None);
                assert_eq!(y.decrease_toward(x), None);
            } else {
                assert_eq!(x.increase_toward(y), Some(x + 1));
                assert_eq!(y.decrease_toward(x), Some(y - 1));
            }
        }

        // Smoke test isize and usize: they're the same as one of the
        // regular integer types, so not worth fuzzing individually.
        // However, we still want some coverage.
        #[test]
        fn test_increase_isize(x: isize) {
            assert_eq!(<isize as Endpoint>::max_value(), isize::MAX);

            if x != isize::MAX {
                assert_eq!(x.next_after(), Some(x + 1));
            } else {
                assert_eq!(x.next_after(), None);
            }
        }

        #[test]
        fn test_decrease_isize(x: isize) {
            assert_eq!(<isize as Endpoint>::min_value(), isize::MIN);

            if x != isize::MIN {
                assert_eq!(x.prev_before(), Some(x - 1));
            } else {
                assert_eq!(x.prev_before(), None);
            }
        }

        #[test]
        fn test_toward_isize(x: isize, y: isize) {
            let (x, y) = (x.min(y), x.max(y));

            assert_eq!(x.decrease_toward(y), None);
            assert_eq!(y.increase_toward(x), None);

            if x == y {
                assert_eq!(x.increase_toward(y), None);
                assert_eq!(x.decrease_toward(y), None);
                assert_eq!(y.increase_toward(x), None);
                assert_eq!(y.decrease_toward(x), None);
            } else {
                assert_eq!(x.increase_toward(y), Some(x + 1));
                assert_eq!(y.decrease_toward(x), Some(y - 1));
            }
        }

        #[test]
        fn test_increase_usize(x: usize) {
            assert_eq!(<usize as Endpoint>::max_value(), usize::MAX);

            if x != usize::MAX {
                assert_eq!(x.next_after(), Some(x + 1));
            } else {
                assert_eq!(x.next_after(), None);
            }
        }

        #[test]
        fn test_decrease_usize(x: usize) {
            assert_eq!(<usize as Endpoint>::min_value(), 0usize);

            if x != usize::MIN {
                assert_eq!(x.prev_before(), Some(x - 1));
            } else {
                assert_eq!(x.prev_before(), None);
            }
        }

        #[test]
        fn test_toward_usize(x: usize, y: usize) {
            let (x, y) = (x.min(y), x.max(y));

            assert_eq!(x.decrease_toward(y), None);
            assert_eq!(y.increase_toward(x), None);

            if x == y {
                assert_eq!(x.increase_toward(y), None);
                assert_eq!(x.decrease_toward(y), None);
                assert_eq!(y.increase_toward(x), None);
                assert_eq!(y.decrease_toward(x), None);
            } else {
                assert_eq!(x.increase_toward(y), Some(x + 1));
                assert_eq!(y.decrease_toward(x), Some(y - 1));
            }
        }
    }
}
