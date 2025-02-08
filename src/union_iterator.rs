//! Computes the union of two normalized iterators.
use crate::ClosedRange;
use crate::Endpoint;
use crate::IntoNormalizedRangeIter;
use crate::NormalizedRangeIter;
use crate::RangeVec;

use std::iter::Peekable;

pub struct UnionIterator<T, X, Y>
where
    T: Endpoint,
    X: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange<EndT = T>>,
    Y: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange<EndT = T>>,
{
    accumulator: Option<(T, T)>,
    left: Peekable<X>,
    right: Peekable<Y>,
}

impl<T, X, Y> UnionIterator<T, X, Y>
where
    T: Endpoint,
    X: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange<EndT = T>>,
    Y: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange<EndT = T>>,
{
    pub fn new(left: X, right: Y) -> Self {
        Self {
            accumulator: None,
            left: left.peekable(),
            right: right.peekable(),
        }
    }
}

impl<T, X, Y> Iterator for UnionIterator<T, X, Y>
where
    T: Endpoint,
    X: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange<EndT = T>>,
    Y: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange<EndT = T>>,
{
    type Item = (T, T);

    fn next(&mut self) -> Option<(T, T)> {
        use std::cmp::Ordering; // Safe because both iterators are normalized

        loop {
            let next;

            match (
                self.left.peek().map(|x| x.get()),
                self.right.peek().map(|x| x.get()),
            ) {
                (Some(left), Some(right)) if T::cmp_range(left, right) <= Ordering::Equal => {
                    next = left;
                    self.left.next();
                }
                (Some(_), Some(right)) => {
                    next = right;
                    self.right.next();
                }
                (Some(x), None) => {
                    next = x;
                    self.left.next();
                }
                (None, Some(x)) => {
                    next = x;
                    self.right.next();
                }
                (None, None) => return self.accumulator.take(),
            };

            let (next_start, next_stop) = next;
            let Some((acc_start, acc_stop)) = self.accumulator.take() else {
                self.accumulator = Some(next);
                continue;
            };

            // Try to join `acc <= next`.
            if let Some(min_start) = acc_stop.increase_toward(next_start) {
                // They're disjoint, produce `acc`, buffer `next.
                if next_start.cmp_end(min_start) > Ordering::Equal {
                    self.accumulator = Some(next);
                    return Some((acc_start, acc_stop));
                }
            }

            self.accumulator = Some((acc_start, acc_stop.top_end(next_stop)));
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (left_min, left_max) = self.left.size_hint();
        let (right_min, right_max) = self.right.size_hint();

        let max = left_max
            .unwrap_or(usize::MAX)
            .checked_add(right_max.unwrap_or(usize::MAX));
        // If both are empty, the union is empty.  Otherwise,
        // they could end up as a single big range.
        let min = ((left_min != 0) | (right_min != 0)) as usize;
        (min, max)
    }
}

impl<T, X, Y> crate::private::Sealed for UnionIterator<T, X, Y>
where
    T: Endpoint,
    X: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange<EndT = T>>,
    Y: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange<EndT = T>>,
{
}

impl<T, X, Y> NormalizedRangeIter for UnionIterator<T, X, Y>
where
    T: Endpoint,
    X: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange<EndT = T>>,
    Y: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange<EndT = T>>,
{
}

impl<T: Endpoint> RangeVec<T> {
    /// Constructs the union of this [`RangeVec`] and any iterator of
    /// ranges.
    ///
    /// See [`union_vec`] for more general types.
    ///
    /// [`union_vec`]: crate::union_vec
    #[inline(always)]
    pub fn union(&self, other: impl IntoNormalizedRangeIter<Item: ClosedRange<EndT = T>>) -> Self {
        #[inline(never)]
        fn doit<T: Endpoint>(
            this: &RangeVec<T>,
            other: impl NormalizedRangeIter<Item: ClosedRange<EndT = T>>,
        ) -> RangeVec<T> {
            this.iter().union(other).collect_range_vec()
        }

        doit(self, other.into_iter())
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod test {
    use super::*;

    #[test]
    fn test_union_iterator_smoke() {
        use crate::NormalizedRangeIter;

        let acc = vec![(1u8, 4u8), (5u8, 1u8), (5u8, 10u8)];
        let src = [(0u8, 2u8), (11u8, 15u8)];

        assert_eq!(
            crate::normalize_vec(acc.clone())
                .iter()
                .union(crate::normalize_vec(src.to_vec()).into_iter())
                .collect_range_vec()
                .into_inner(),
            vec![(0u8, 15u8)]
        );

        assert_eq!(
            crate::normalize_vec(src.to_vec())
                .iter()
                .union(crate::normalize_vec(vec![]))
                .collect_range_vec()
                .into_inner(),
            src.to_vec()
        );
    }

    proptest::proptest! {
        #[test]
        fn test_union_iterator(xs: Vec<(u8, u8)>, ys: Vec<(u8, u8)>)
        {
            use crate::RangeVec;
            use crate::ranges_to_bits;

            let bits = {
                let mut all_ranges = xs.clone();
                all_ranges.extend(&ys);
                ranges_to_bits(&all_ranges)
            };

            let xs = RangeVec::from_vec(xs);
            let ys = RangeVec::from_vec(ys);

            {
                let union = xs.iter().union(ys.iter());

                let (min_size, max_size) = union.size_hint();
                if !xs.is_empty() || !ys.is_empty() {
                    assert!(min_size > 0);
                } else {
                    assert!(min_size == 0);
                }

                let max_size = max_size.expect("should have limits");
                assert!(max_size == xs.len() + ys.len());

                let union = union.collect_range_vec();
                assert_eq!(bits, ranges_to_bits(&union));
            }

            {
                let union = ys.iter().union(xs).collect_range_vec();
                assert_eq!(bits, ranges_to_bits(&union));
            }
        }

        #[test]
        fn test_union_iterator_identities(xs: Vec<(u8, u8)>)
        {
            let xs = RangeVec::from_vec(xs);

            // xs | xs = xs
            {
                let xxs = xs.iter().union(xs.iter()).collect_range_vec();
                assert_eq!(&xxs, &xs);
            }

            // xs | -xs = universe
            let universe = xs.iter().union(xs.iter().complement()).collect_range_vec();
            assert_eq!(universe.inner(), &[(0, 255u8)]);
        }
    }
}
