use crate::ClosedRange;
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
    Ranges: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange>,
{
    state: Option<(
        ComplementGenerator<<<Ranges as Iterator>::Item as ClosedRange>::EndT>,
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

type Pair<T> = (T, T);

impl<Ranges> Iterator for ComplementIterator<Ranges>
where
    Ranges: Sized + NormalizedRangeIter + Iterator<Item: ClosedRange>,
{
    type Item = Pair<<<Ranges as Iterator>::Item as ClosedRange>::EndT>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (self_cg, ranges) = self.state.as_mut()?;
            let mut cg = ComplementGenerator::new();
            std::mem::swap(&mut cg, self_cg);

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

#[inline(never)]
fn complement_impl<T: Endpoint>(normalized_intervals: Vec<(T, T)>) -> RangeVec<T> {
    let mut intervals = normalized_intervals;
    let mut prefix_len = 0;

    'out: {
        let mut cg = ComplementGenerator::new();

        for i in 0..intervals.len() {
            assert!(prefix_len <= i);
            let (start, stop) = intervals[i];

            // The input is normalized, so intervals are valid.
            debug_assert!(start <= stop);

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

/// Returns the complement of a vector of of closed `intervals`.
#[inline(always)]
pub fn complement_vec<T: Endpoint>(intervals: impl Into<RangeCase<T>>) -> RangeVec<T> {
    crate::normalize_vec(intervals).into_complement()
}

impl<T: Endpoint> RangeVec<T> {
    /// Constructs the complement of [`RangeVec`] in a fresh vector.
    #[inline(always)]
    pub fn complement(&self) -> RangeVec<T> {
        self.iter().complement().collect_range_vec()
    }

    /// Complements this [`RangeVec`] in place.
    #[inline(always)]
    pub fn into_complement(self) -> RangeVec<T> {
        complement_impl(self.into_inner())
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod test {
    use super::*;

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
            complement_vec(empty.to_vec()).into_inner(),
            vec![(0u8, 255u8)]
        );
        assert_eq!(
            normalize_vec(empty.to_vec()).into_complement().into_inner(),
            vec![(0u8, 255u8)]
        );

        assert_eq!(
            normalize_vec(empty.to_vec()).complement().into_inner(),
            vec![(0u8, 255u8)]
        );

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

        assert_eq!(
            complement_vec(vec![(1u8, 10u8), (11u8, 11u8)]).into_inner(),
            vec![(0u8, 0u8), (12u8, 255u8)]
        );
        assert_eq!(
            complement(&normalize_vec(vec![(1u8, 10u8), (11u8, 11u8)]))
                .collect_range_vec()
                .into_inner(),
            vec![(0u8, 0u8), (12u8, 255u8)]
        );

        assert_eq!(
            complement_vec(vec![(1u8, 255u8)]).into_inner(),
            vec![(0u8, 0u8)]
        );
        assert_eq!(
            complement(&normalize_vec(vec![(1u8, 255u8)]))
                .collect_range_vec()
                .into_inner(),
            vec![(0u8, 0u8)]
        );

        assert_eq!(
            complement_vec(vec![(1u8, 254u8)]).into_inner(),
            vec![(0u8, 0u8), (255u8, 255u8)]
        );
        assert_eq!(
            complement(&normalize_vec(vec![(1u8, 254u8)]))
                .collect_range_vec()
                .into_inner(),
            vec![(0u8, 0u8), (255u8, 255u8)]
        );
        assert_eq!(
            complement(normalize_vec(vec![(1u8, 254u8)]))
                .collect_range_vec()
                .into_inner(),
            vec![(0u8, 0u8), (255u8, 255u8)]
        );

        assert_eq!(complement_vec(vec![(0u8, 255u8)]).into_inner(), vec![]);
        assert_eq!(
            complement(normalize_vec(vec![(0u8, 255u8)]))
                .collect_range_vec()
                .into_inner(),
            vec![]
        );

        assert_eq!(
            complement_vec(vec![(0u8, 254u8)]).into_inner(),
            vec![(255u8, 255u8)]
        );
        assert_eq!(
            complement(normalize_vec(vec![(0u8, 254u8)])).collect::<Vec<_>>(),
            vec![(255u8, 255u8)]
        );

        assert_eq!(
            complement(&normalize_vec(vec![(0u8, 254u8)]))
                .collect_range_vec()
                .into_inner(),
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
    }
}
