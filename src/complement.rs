use crate::Backing;
use crate::ClosedRange;
use crate::ClosedRangeEnd;
use crate::ClosedRangeVal;
use crate::Endpoint;
use crate::NormalizedRangeIter;
use crate::RangeCase;
use crate::RangeVec;

// Not an actual rust generator, but one day...
#[repr(transparent)]
struct ComplementGenerator<T: Endpoint> {
    next_start: T,
}

impl<T: Endpoint> ComplementGenerator<T> {
    #[inline(always)]
    fn new() -> Self {
        Self {
            next_start: T::min_value(),
        }
    }

    #[inline(always)]
    fn next(self, range: (T, T)) -> (Option<Self>, Option<(T, T)>) {
        let next_start = self.next_start;
        let (start, stop) = range;
        // next_start <= start <= stop
        //     |           [        ]
        //     ^.........^
        //     [         ]
        //     gap interval
        // Generate the next item if we can find a gap between `next_start` and `start`
        let gap = start
            .decrease_toward(next_start)
            .map(|prev| (next_start, prev));

        let next_self = stop.next_after().map(|next_start| Self { next_start });

        (next_self, gap)
    }

    #[inline(always)]
    fn end(self) -> (T, T) {
        (self.next_start, T::max_value())
    }
}

pub struct ComplementIterator<Ranges>
where
    // No need to keep this fused: we reset `state = None` when the iterator stops.
    Ranges: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange>,
{
    state: Option<(
        ComplementGenerator<ClosedRangeEnd<<Ranges as Iterator>::Item>>,
        Ranges,
    )>,
}

impl<Ranges> ComplementIterator<Ranges>
where
    Ranges: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange>,
{
    #[inline(always)]
    pub fn new(ranges: Ranges) -> Self {
        Self {
            state: Some((ComplementGenerator::new(), ranges)),
        }
    }
}

impl<Ranges> Iterator for ComplementIterator<Ranges>
where
    Ranges: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange>,
{
    type Item = ClosedRangeVal<<Ranges as Iterator>::Item>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (self_cg, ranges) = self.state.as_mut()?;
            let mut cg = ComplementGenerator::new();
            core::mem::swap(&mut cg, self_cg);

            let Some(range) = ranges.next() else {
                self.state = None;
                return Some(cg.end());
            };

            let (cg, ret) = cg.next(range.get());
            match cg {
                None => {
                    self.state = None;
                    return ret;
                }
                Some(cg) => {
                    *self_cg = cg;
                }
            }

            if ret.is_some() {
                return ret;
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (min, max) = match self.state.as_ref() {
            Some((_, ranges)) => ranges.size_hint(),
            None => (0, None),
        };

        // we know there is one gap between each entry in ranges, so
        // so we'll generate at least n - 1 gaps.
        //
        // In the worst case, we can also add two gaps on both ends.
        (min.saturating_sub(1), max.map(|max| max.saturating_add(2)))
    }
}

impl<Ranges> crate::private::Sealed for ComplementIterator<Ranges> where
    Ranges: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange>
{
}

impl<Ranges> NormalizedRangeIter for ComplementIterator<Ranges> where
    Ranges: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange>
{
}

// We explicitly clear our state when get to the end, so we reliably
// keep returning `None`.
impl<Ranges> core::iter::FusedIterator for ComplementIterator<Ranges> where
    Ranges: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange>
{
}

#[inline(never)]
fn complement_impl<T: Endpoint>(normalized_intervals: Backing<T>) -> RangeVec<T> {
    // safe to compare ranges because they're normalized.
    use core::cmp::Ordering;

    let mut intervals = normalized_intervals;
    let mut prefix_len = 0;

    'out: {
        let mut cg = ComplementGenerator::new();

        for i in 0..intervals.len() {
            assert!(prefix_len <= i);
            let (start, stop) = intervals[i];

            // The input is normalized, so intervals are valid.
            debug_assert!(start.cmp_end(stop) <= Ordering::Equal);

            let (next_cg, gap) = cg.next(intervals[i]);
            if let Some(gap) = gap {
                intervals[prefix_len] = gap;
                prefix_len += 1;
            }

            match next_cg {
                Some(next_cg) => cg = next_cg,
                None => {
                    intervals.truncate(prefix_len);
                    break 'out;
                }
            }
        }

        let final_interval = cg.end();
        if prefix_len < intervals.len() {
            intervals[prefix_len] = final_interval;
            intervals.truncate(prefix_len + 1);
        } else {
            intervals.push(final_interval);
        }
    }

    unsafe { RangeVec::new_unchecked(intervals) }
}

/// Returns the complement of a vector of closed `intervals`.
///
/// This operation is in-place and takes time linear in the input if
/// it is already normalized, and \\(\mathcal{O}(n \log n)\\) time
/// otherwise.
#[inline(always)]
#[must_use]
pub fn complement_vec<T: Endpoint>(intervals: impl Into<RangeCase<T>>) -> RangeVec<T> {
    crate::normalize_vec(intervals).into_complement()
}

impl<T: Endpoint> RangeVec<T> {
    /// Constructs the complement of [`RangeVec`] in a fresh vector.
    ///
    /// This operation takes linear time and allocates the result at
    /// most in linear space.
    #[inline(always)]
    #[must_use]
    pub fn complement(&self) -> RangeVec<T> {
        self.iter().complement().collect_range_vec()
    }

    /// Complements this [`RangeVec`] in place.
    ///
    /// This operation is in place and takes linear time.
    #[inline(always)]
    #[must_use]
    pub fn into_complement(self) -> RangeVec<T> {
        #[cfg(feature = "internal_checks")]
        let expected = self.complement();

        let ret = complement_impl(self.into_inner());
        #[cfg(feature = "internal_checks")]
        assert!(&expected.eqv(&ret));

        ret
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod test {
    use super::*;
    use alloc::vec;
    use alloc::vec::Vec;
    use smallvec::smallvec;

    #[test]
    fn test_complement_smoke() {
        use crate::normalize_vec;
        use crate::IntoNormalizedRangeIter;

        fn complement(
            x: impl IntoNormalizedRangeIter<Item = (u8, u8)>,
        ) -> impl NormalizedRangeIter<Item = (u8, u8)> {
            x.into_iter().complement()
        }

        let empty: &[(u8, u8)] = &[];
        assert_eq!(
            complement_vec(empty.to_vec()).into_vec(),
            vec![(0u8, 255u8)]
        );
        assert_eq!(
            normalize_vec(empty.to_vec()).into_complement().into_vec(),
            vec![(0u8, 255u8)]
        );

        assert_eq!(
            normalize_vec(empty.to_vec()).complement().into_vec(),
            vec![(0u8, 255u8)]
        );

        {
            let mut universe = normalize_vec(empty.to_vec()).into_iter().complement();

            assert_eq!(universe.next(), Some((0u8, 255u8)));
            assert_eq!(universe.next(), None); // Then we keep being done.
            assert_eq!(universe.next(), None);
        }

        {
            let (min, max) = complement(normalize_vec(empty.to_vec())).size_hint();

            assert!(min <= 1);
            assert!(max.expect("should have max") >= 1);
        }

        {
            let (min, max) = complement(normalize_vec(vec![(1u8, 10u8), (11u8, 11u8)])).size_hint();

            assert!(min <= 2);
            assert!(max.expect("should have max") >= 2);
        }

        let smallvec: smallvec::SmallVec<[_; crate::INLINE_SIZE]> =
            smallvec![(1u8, 10u8), (11u8, 11u8)];
        assert_eq!(
            complement_vec(smallvec).into_vec(),
            vec![(0u8, 0u8), (12u8, 255u8)]
        );
        assert_eq!(
            complement(&normalize_vec(vec![(1u8, 10u8), (11u8, 11u8)]))
                .collect_range_vec()
                .into_vec(),
            vec![(0u8, 0u8), (12u8, 255u8)]
        );

        let largervec: smallvec::SmallVec<[_; crate::INLINE_SIZE + 1]> = smallvec![(1u8, 255u8)];
        assert_eq!(complement_vec(largervec).into_vec(), vec![(0u8, 0u8)]);

        let smallervec: smallvec::SmallVec<[_; crate::INLINE_SIZE.saturating_sub(1)]> =
            smallvec![(1u8, 255u8)];
        assert_eq!(
            complement(&normalize_vec(smallervec))
                .collect_range_vec()
                .into_vec(),
            vec![(0u8, 0u8)]
        );

        assert_eq!(
            complement_vec(vec![(1u8, 254u8)]).into_vec(),
            vec![(0u8, 0u8), (255u8, 255u8)]
        );
        assert_eq!(
            complement(&normalize_vec(vec![(1u8, 254u8)]))
                .collect_range_vec()
                .into_vec(),
            vec![(0u8, 0u8), (255u8, 255u8)]
        );
        assert_eq!(
            complement(normalize_vec(vec![(1u8, 254u8)]))
                .collect_range_vec()
                .into_vec(),
            vec![(0u8, 0u8), (255u8, 255u8)]
        );

        assert_eq!(complement_vec(vec![(0u8, 255u8)]).into_vec(), vec![]);
        assert_eq!(
            complement(normalize_vec(vec![(0u8, 255u8)]))
                .collect_range_vec()
                .into_vec(),
            vec![]
        );

        assert_eq!(
            complement_vec(vec![(0u8, 254u8)]).into_vec(),
            vec![(255u8, 255u8)]
        );
        assert_eq!(
            complement(normalize_vec(vec![(0u8, 254u8)])).collect::<Vec<_>>(),
            vec![(255u8, 255u8)]
        );

        assert_eq!(
            complement(&normalize_vec(vec![(0u8, 254u8)]))
                .collect_range_vec()
                .into_vec(),
            vec![(255u8, 255u8)]
        );
    }

    proptest::proptest! {
        #[test]
        fn test_increase(ranges: Vec<(u8, u8)>) {
            use crate::ranges_to_bits;

            let marks = ranges_to_bits(&ranges).into_iter().map(|x| !x).collect::<Vec<bool>>();

            assert_eq!(&ranges_to_bits(&complement_vec(ranges.clone())), &marks);

            let ranges = RangeVec::from_vec(ranges);
            assert_eq!(&ranges_to_bits(&complement_vec(ranges.clone())), &marks);

            assert_eq!(&ranges_to_bits(&ranges.clone().complement()), &marks);
            assert_eq!(&ranges_to_bits(&ranges.clone().into_complement()), &marks);

            assert_eq!(&ranges_to_bits(&ranges.iter().complement().collect_range_vec()), &marks);
        }

        #[test]
        fn test_self_inverse_f32(ranges: Vec<(f32, f32)>) {
            let ranges = RangeVec::from_vec(ranges);
            let complement = ranges.complement();
            let double_complement = complement.into_complement();

            assert_eq!(ranges, double_complement);
        }

        #[test]
        fn test_self_inverse_f64(ranges: Vec<(f64, f64)>) {
            let ranges = RangeVec::from_vec(ranges);
            let complement = ranges.complement();
            let double_complement = complement.into_complement();

            assert_eq!(ranges, double_complement);
        }
    }
}
