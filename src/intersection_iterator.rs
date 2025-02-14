//! Computes the union of two normalized iterators.
use crate::ClosedRange;
use crate::Endpoint;
use crate::IntoNormalizedRangeIter;
use crate::NormalizedRangeIter;
use crate::RangeVec;

use core::iter::Peekable;

pub struct LinearIntersectionIterator<T, X, Y>
where
    T: Endpoint,
    X: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange<EndT = T>>,
    Y: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange<EndT = T>>,
{
    left: Peekable<X>,
    right: Peekable<Y>,
}

impl<T, X, Y> LinearIntersectionIterator<T, X, Y>
where
    T: Endpoint,
    X: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange<EndT = T>>,
    Y: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange<EndT = T>>,
{
    pub fn new(left: X, right: Y) -> Self {
        Self {
            left: left.peekable(),
            right: right.peekable(),
        }
    }
}

impl<T, X, Y> Iterator for LinearIntersectionIterator<T, X, Y>
where
    T: Endpoint,
    X: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange<EndT = T>>,
    Y: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange<EndT = T>>,
{
    type Item = (T, T);

    fn next(&mut self) -> Option<(T, T)> {
        use core::cmp::Ordering; // Safe because both iterators are normalized

        loop {
            let (Some(left), Some(right)) = (
                self.left.peek().map(|x| x.get()),
                self.right.peek().map(|x| x.get()),
            ) else {
                return None;
            };

            // We always advance the smallest endpoint (or both if equal)
            match left.1.cmp_end(right.1) {
                Ordering::Less => {
                    self.left.next();
                }
                Ordering::Equal => {
                    self.left.next();
                    self.right.next();
                }
                Ordering::Greater => {
                    self.right.next();
                }
            }

            // Find the intersection of left and right.
            let start = left.0.top_end(right.0);
            let stop = left.1.bot_end(right.1);

            if start.cmp_end(stop) <= Ordering::Equal {
                return Some((start, stop));
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        // The intersection can always be empty, but each output range
        // consumed (at least) one input range.
        let (_, left_max) = self.left.size_hint();
        let (_, right_max) = self.right.size_hint();

        if (left_max == Some(0)) | (right_max == Some(0)) {
            // Intersection with empty is always empty.
            (0, Some(0))
        } else {
            (
                0,
                left_max
                    .unwrap_or(usize::MAX)
                    .checked_add(right_max.unwrap_or(usize::MAX)),
            )
        }
    }
}

impl<T, X, Y> crate::private::Sealed for LinearIntersectionIterator<T, X, Y>
where
    T: Endpoint,
    X: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange<EndT = T>>,
    Y: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange<EndT = T>>,
{
}

impl<T, X, Y> NormalizedRangeIter for LinearIntersectionIterator<T, X, Y>
where
    T: Endpoint,
    X: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange<EndT = T>>,
    Y: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange<EndT = T>>,
{
}

// We use `Peekable` internally, so we'll reliably return None after None.
impl<T, X, Y> core::iter::FusedIterator for LinearIntersectionIterator<T, X, Y>
where
    T: Endpoint,
    X: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange<EndT = T>>,
    Y: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange<EndT = T>>,
{
}

impl<T: Endpoint> RangeVec<T> {
    /// Constructs the intersection of this [`RangeVec`] and any iterator of
    /// ranges.
    ///
    /// This operation takes linear time in the size of the two inputs.
    ///
    /// See [`RangeVec::intersect_vec`] when the other argument is
    /// also a [`RangeVec`].
    #[inline(always)]
    #[must_use]
    pub fn intersect(
        &self,
        other: impl IntoNormalizedRangeIter<Item: ClosedRange<EndT = T>>,
    ) -> Self {
        #[inline(never)]
        fn doit<T: Endpoint>(
            this: &RangeVec<T>,
            other: impl NormalizedRangeIter<Item: ClosedRange<EndT = T>>,
        ) -> RangeVec<T> {
            let iter = this.iter().intersect(other);
            let size_hint = iter.size_hint();
            if this.is_empty() {
                debug_assert_eq!(size_hint, (0, Some(0)));
            }

            let ret = iter.collect_range_vec();

            debug_assert!(ret.len() >= size_hint.0);
            debug_assert!(ret.len() <= size_hint.1.unwrap_or(usize::MAX));

            ret
        }

        doit(self, other.into_iter())
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod test {
    use super::*;
    use alloc::vec;
    use alloc::vec::Vec;

    #[test]
    fn smoke_test() {
        // empty & empty -> empty.
        let empty: RangeVec<u8> = RangeVec::default();
        let other = RangeVec::from_vec(vec![(u8::MIN, u8::MAX)]);

        {
            let empty_empty = empty.iter().intersect(empty.iter());

            assert_eq!(empty_empty.size_hint(), (0, Some(0)));
            assert_eq!(&empty_empty.collect_range_vec(), &empty);
        }

        {
            let empty_other = empty.iter().intersect(other.iter());

            assert_eq!(empty_other.size_hint(), (0, Some(0)));
            assert_eq!(&empty_other.collect_range_vec(), &empty);
        }

        {
            let other_empty = other.iter().intersect(empty.iter());

            assert_eq!(other_empty.size_hint(), (0, Some(0)));
            assert_eq!(&other_empty.collect_range_vec(), &empty);
        }

        // We can pull multiple times and get `None`.
        {
            let mut other_empty = other.iter().intersect(other.iter());

            // We can't know it's empty.
            assert!(other_empty.size_hint() != (0, Some(0)));

            assert!(other_empty.next().is_some());
            // Should be done
            assert_eq!(other_empty.next(), None);
            // And still done.
            assert_eq!(other_empty.next(), None);
        }
    }

    #[cfg(test)]
    proptest::proptest! {
        #[test]
        fn test_intersection_iterator(xs: Vec<(u8, u8)>, ys: Vec<(u8, u8)>)
        {
            use crate::ranges_to_bits;

            let bits = {
                let x_bits = ranges_to_bits(&xs);
                let y_bits = ranges_to_bits(&ys);

                x_bits.into_iter().zip(y_bits.into_iter()).map(|(x, y)| x & y).collect::<Vec<bool>>()
            };

            {
                let out = RangeVec::from_vec(xs.clone()).iter().intersect(
                    RangeVec::from_vec(ys.clone()).iter()).collect_range_vec();
                assert_eq!(&bits, &ranges_to_bits(&out));
            }

            {
                let out = RangeVec::from_vec(ys.clone()).iter().intersect(&RangeVec::from_vec(xs.clone())).collect_range_vec();
                assert_eq!(&bits, &ranges_to_bits(&out));
            }
        }

        #[test]
        fn test_intersection_identity(xs: Vec<(u8, u8)>, ys: Vec<(u8, u8)>)
        {
            // Increase interesting coverage with valid ranges
            let xs = RangeVec::from_vec(xs.into_iter().map(|(a, b)| (a.min(b), a.max(b))).collect::<Vec<_>>());
            let ys = RangeVec::from_vec(ys.into_iter().map(|(a, b)| (a.min(b), a.max(b))).collect::<Vec<_>>());

            //  (X & Y) = -(-x | -y),
            // or
            // -(X & Y) =  (-x | -y).

            // Try that with iterators.
            {
                let not_and = xs.iter().intersect(&ys).complement().collect_range_vec();
                let or_not = crate::union_vec(xs.iter().complement().collect_range_vec(),
                                              ys.iter().complement());

                assert_eq!(not_and, or_not);
            }

            {
                let and = xs.iter().intersect(&ys).collect_range_vec();
                let not_or_not = crate::union_vec(xs.iter().complement().collect_range_vec(),
                                                  ys.iter().complement()).iter().complement().collect_range_vec();

                assert_eq!(and, not_or_not);
            }
        }
    }
}
