use crate::slice_sequence::Sequence;
use crate::ClosedRange;
use crate::ClosedRangeVal;
use crate::Endpoint;
use crate::NormalizedRangeIter;
use crate::Pair;
use crate::RangeVec;

/// The core [`IntersectorImpl`] works over [`Sequence`] rather than
/// raw slices because the standard slice interface is full of hidden
/// panics; the [`Sequence`] trait is small enough to audit, and
/// doesn't itself hide panics in its interface.
///
/// The underlying [`Sequence`] must come from a normalized `RangeVec`.
struct IntersectorImpl<Seq: Sequence> {
    seq: Seq,
    search_cursor: Seq,
    intersect_cursor: Seq,
}

impl<Seq: Sequence> IntersectorImpl<Seq> {
    #[inline(always)]
    fn new(seq: Seq) -> Self {
        Self {
            seq,
            search_cursor: seq,
            intersect_cursor: seq,
        }
    }

    #[inline(always)]
    fn start_search(&mut self, start: Seq::EndT) {
        self.search_cursor = self.seq.skip_to((start, start), self.search_cursor);
        self.intersect_cursor = self.search_cursor;
    }

    fn pump(&mut self, needle: Pair<Seq::EndT>) -> Option<Pair<Seq::EndT>> {
        // Safe to compare because `seq` and its cursors are normalized.
        use core::cmp::Ordering;

        let (x_start, x_stop) = needle;

        while let Some(((y_start, y_stop), rest)) = self.intersect_cursor.uncons() {
            self.intersect_cursor = rest;

            if y_start.cmp_end(x_stop) == Ordering::Greater {
                return None;
            }

            let start = x_start.top_end(y_start);
            let stop = x_stop.bot_end(y_stop);

            if start.cmp_end(stop) <= Ordering::Equal {
                return Some((start, stop));
            }
        }

        None
    }
}

#[repr(transparent)]
pub struct Intersector<'a, T: Endpoint>(IntersectorImpl<&'a [(T, T)]>);

impl<'a, T: Endpoint> Intersector<'a, T> {
    #[inline(always)]
    fn new(seq: &'a [(T, T)]) -> Self {
        Self(IntersectorImpl::new(seq))
    }

    #[inline(always)]
    fn start_search(&mut self, start: T) {
        self.0.start_search(start)
    }

    #[inline(always)]
    fn pump(&mut self, needle: (T, T)) -> Option<(T, T)> {
        self.0.pump(needle)
    }
}

pub struct IntersectionIterator<'a, Xs: NormalizedRangeIter> {
    // No need to fuse: we only call `next` after `None` when
    // we're called after returning `None`
    xs: Xs,
    intersector: Intersector<'a, <<Xs as Iterator>::Item as ClosedRange>::EndT>,
    curr: Option<ClosedRangeVal<<Xs as Iterator>::Item>>,
}

impl<'a, Xs: NormalizedRangeIter> IntersectionIterator<'a, Xs> {
    #[inline(always)]
    fn new(xs: Xs, ys: &'a [ClosedRangeVal<<Xs as Iterator>::Item>]) -> Self {
        Self {
            xs,
            intersector: Intersector::new(ys),
            curr: None,
        }
    }
}

impl<Xs: NormalizedRangeIter> Iterator for IntersectionIterator<'_, Xs> {
    type Item = ClosedRangeVal<<Xs as Iterator>::Item>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let curr = match self.curr {
                Some(curr) => curr,
                None => {
                    let next = self.xs.next()?.get();
                    self.intersector.start_search(next.0);
                    self.curr = Some(next);
                    next
                }
            };

            if let Some(ret) = self.intersector.pump(curr) {
                return Some(ret);
            }

            self.curr = None;
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        // The intersection can always be empty, but each output range
        // consumed (at least) one input range.
        let (_, x_max) = self.xs.size_hint();
        let y_max = self.intersector.0.search_cursor.len();

        if (x_max == Some(0)) | (y_max == 0) {
            (0, Some(0))
        } else {
            (0, x_max.unwrap_or(usize::MAX).checked_add(y_max))
        }
    }
}

impl<Xs: NormalizedRangeIter> crate::private::Sealed for IntersectionIterator<'_, Xs> {}

impl<Xs: NormalizedRangeIter> crate::NormalizedRangeIter for IntersectionIterator<'_, Xs> {}

impl<Xs: NormalizedRangeIter + core::iter::FusedIterator> core::iter::FusedIterator
    for IntersectionIterator<'_, Xs>
{
}

/// This internal implementation assumes `ys` is normalised.
#[inline(always)]
pub(crate) unsafe fn intersect<Xs: NormalizedRangeIter>(
    xs: Xs,
    ys: &[ClosedRangeVal<<Xs as Iterator>::Item>],
) -> IntersectionIterator<'_, Xs> {
    IntersectionIterator::new(xs, ys)
}

impl<T: Endpoint> RangeVec<T> {
    /// Constructs the intersection of this [`RangeVec`] and another
    /// [`RangeVec`].
    ///
    /// This operation takes at most \\(\mathcal{O}(\min(m + n, m \log n))\\)
    /// time, where \\(m\\) is the size of `self`, and \\(n\\) that of `other`.
    #[inline(always)]
    pub fn intersect_vec<'a>(&'a self, other: &'a RangeVec<T>) -> Self {
        intersect_vec(self, other)
    }
}
/// Constructs the intersection of two normalized vectors of ranges.
///
/// Since both arguments are guaranteed to be normalized, we can
/// iterate over the shorter one and binary search over the longer
/// one, which is usually a good idea.
///
/// This operation takes at most \\(\mathcal{O}(\min(m + n, m \log n))\\)
/// time, where \\(m\\) is the size of the shorter [`RangeVec`], and
/// \\(n\\) that of the longer [`RangeVec`].
#[inline(never)]
pub fn intersect_vec<'a, T: Endpoint>(
    mut xs: &'a RangeVec<T>,
    mut ys: &'a RangeVec<T>,
) -> RangeVec<T> {
    #[cfg(feature = "internal_checks")]
    let expected = (
        xs.iter().intersect(ys.iter()).collect_range_vec(),
        ys.iter().intersect(xs.iter()).collect_range_vec(),
        xs.iter().intersect_vec(ys).collect_range_vec(),
        ys.iter().intersect_vec(xs).collect_range_vec(),
    );

    if xs.len() > ys.len() {
        core::mem::swap(&mut xs, &mut ys);
    }

    debug_assert!(xs.len() <= ys.len());
    let intersection = xs.iter().intersect_vec(ys);
    let size_hint = intersection.size_hint();

    let ret = intersection.collect_range_vec();

    // If any input is empty -> we know the intersection is empty.
    debug_assert!((!(xs.is_empty() | ys.is_empty())) | (size_hint == (0, Some(0))));
    debug_assert!(size_hint.0 <= ret.len());
    debug_assert!(ret.len() <= size_hint.1.unwrap());

    #[cfg(feature = "internal_checks")]
    {
        assert!(&expected.0.eqv(&ret));
        assert!(&expected.1.eqv(&ret));
        assert!(&expected.2.eqv(&ret));
        assert!(&expected.3.eqv(&ret));
    }

    ret
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod test {
    use super::*;
    use alloc::vec;
    use alloc::vec::Vec;

    #[test]
    fn test_smoke() {
        // intersection of two empty sets -> empty set
        assert!(crate::normalize_vec(Vec::<(u8, u8)>::new())
            .iter()
            .intersect_vec(&crate::normalize_vec(Vec::<(u8, u8)>::new()))
            .collect_range_vec()
            .is_empty());

        let xs = crate::normalize_vec(vec![(1u8, 1u8), (3u8, 4u8), (10u8, 20u8), (30u8, 100u8)]);
        let ys = crate::normalize_vec(vec![
            (0u8, 6u8),
            (8u8, 15u8),
            (17u8, 18u8),
            (20u8, 22u8),
            (200u8, 200u8),
        ]);

        // intersection of anything with empty set -> empty set
        assert!(crate::normalize_vec(Vec::<(u8, u8)>::new())
            .iter()
            .intersect_vec(&xs)
            .collect_range_vec()
            .is_empty());
        assert!(ys
            .clone()
            .intersect(&crate::normalize_vec(Vec::<(u8, u8)>::new()))
            .is_empty());

        assert_eq!(
            xs.clone().intersect(&ys).into_vec(),
            vec![
                (1u8, 1u8),
                (3u8, 4u8),
                (10u8, 15u8),
                (17u8, 18u8),
                (20u8, 20u8)
            ]
        );

        assert_eq!(
            xs.intersect_vec(&ys).into_vec(),
            vec![
                (1u8, 1u8),
                (3u8, 4u8),
                (10u8, 15u8),
                (17u8, 18u8),
                (20u8, 20u8)
            ]
        );

        assert_eq!(
            intersect_vec(&ys, &xs).into_vec(),
            vec![
                (1u8, 1u8),
                (3u8, 4u8),
                (10u8, 15u8),
                (17u8, 18u8),
                (20u8, 20u8)
            ]
        );

        assert_eq!(
            xs.iter().intersect_vec(&ys).collect::<Vec<_>>(),
            vec![
                (1u8, 1u8),
                (3u8, 4u8),
                (10u8, 15u8),
                (17u8, 18u8),
                (20u8, 20u8)
            ]
        );

        assert_eq!(
            ys.iter().intersect_vec(&xs).collect::<Vec<_>>(),
            vec![
                (1u8, 1u8),
                (3u8, 4u8),
                (10u8, 15u8),
                (17u8, 18u8),
                (20u8, 20u8)
            ]
        );

        assert_eq!(
            intersect_vec(
                &crate::normalize_vec(xs[..0].to_vec()),
                &crate::normalize_vec(vec![])
            )
            .into_vec(),
            vec![]
        );

        {
            let empty = crate::normalize_vec(xs[..0].to_vec());

            assert_eq!(
                unsafe { intersect(empty.iter(), &[]) }
                    .collect_range_vec()
                    .into_vec(),
                vec![]
            );
        }

        assert_eq!(
            intersect_vec(
                &crate::normalize_vec(xs[1..2].to_vec()),
                &crate::normalize_vec(vec![(0u8, 0u8)])
            )
            .into_vec(),
            vec![]
        );
    }

    proptest::proptest! {
        #[test]
        fn test_intersection(xs: Vec<(u8, u8)>, ys: Vec<(u8, u8)>)
        {
            use crate::ranges_to_bits;

            let bits = {
                let x_bits = ranges_to_bits(&xs);
                let y_bits = ranges_to_bits(&ys);

                x_bits.into_iter().zip(y_bits.into_iter()).map(|(x, y)| x & y).collect::<Vec<bool>>()
            };

            {
                let out = intersect_vec(&RangeVec::from_vec(xs.clone()),
                                        &RangeVec::from_vec(ys.clone()));
                assert_eq!(&bits, &ranges_to_bits(&out));
            }

            {
                let out = RangeVec::from_vec(ys.clone()).intersect(&RangeVec::from_vec(xs.clone()));
                assert_eq!(&bits, &ranges_to_bits(&out));
            }

            {
                let out = RangeVec::from_vec(xs.clone()).into_iter().intersect_vec(&RangeVec::from_vec(ys.clone())).collect_range_vec();
                assert_eq!(&bits, &ranges_to_bits(&out));
            }

            {
                let out = RangeVec::from_vec(ys.clone()).into_iter().intersect_vec(&RangeVec::from_vec(xs.clone())).collect_range_vec();
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
                let not_and = xs.iter().intersect_vec(&ys).complement().collect_range_vec();
                let or_not = crate::union_vec(xs.iter().complement().collect_range_vec(),
                                              ys.iter().complement());

                assert_eq!(not_and, or_not);
            }

            {
                let and = xs.iter().intersect_vec(&ys).collect_range_vec();
                let not_or_not = crate::union_vec(xs.iter().complement().collect_range_vec(),
                                                  ys.iter().complement()).iter().complement().collect_range_vec();

                assert_eq!(and, not_or_not);
            }

            // Now work with RangeVec as much as possible.
            {
                let not_and = intersect_vec(&xs, &ys).into_complement();
                let or_not = crate::union_vec(xs.clone().into_complement(),
                                              ys.clone().into_complement());

                assert_eq!(not_and, or_not);
            }

            {
                let not_and = intersect_vec(&xs, &ys).into_complement();
                let or_not = xs.clone().into_complement().union(
                    ys.clone().into_complement());

                assert_eq!(not_and, or_not);
            }

            {
                let and = intersect_vec(&xs, &ys);
                let not_or_not = xs.clone().into_complement()
                    .union(ys.clone().into_complement())
                    .into_complement();

                assert_eq!(and, not_or_not);
            }
        }
    }
}
