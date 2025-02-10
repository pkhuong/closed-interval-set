//! A normalized set of intervals consists of a sorted sequence of
//! disjoint intervals.
use crate::Backing;
use crate::ClosedRange;
use crate::Endpoint;
use crate::RangeCase;
use crate::RangeVec;

/// Determines whether the input sequence is in normalized format:
///  1. consists of valid intervals `(start, stop)` with `start <= stop`
///  2. intervals are sorted by the `start` endpoint
///  3. adjacent intervals are disjoint and separated by at least one `Endpoint` value
///
/// Checking this property takes time linear in the length of the input iterator.
#[inline(always)]
pub fn is_normalized<T: Endpoint>(
    intervals: impl IntoIterator<Item: ClosedRange<EndT = T>>,
) -> bool {
    #[inline(never)]
    fn doit<T: Endpoint>(mut iter: impl Iterator<Item: ClosedRange<EndT = T>>) -> bool {
        use std::cmp::Ordering; // Safe because we always check validity, so bogus results are fine

        let mut ret;
        let mut prev_stop;

        // Check the first range, if any.
        match iter.next().map(|range| range.get()) {
            Some((start, stop)) => {
                // Range must be valid.
                ret = start.is_valid() & stop.is_valid();
                ret &= start.cmp_end(stop) <= Ordering::Equal;
                prev_stop = stop;
            }
            // Empty sequence is normalized
            None => return true,
        }

        for (start, stop) in iter.map(|range| range.get()) {
            ret &= start.is_valid() & stop.is_valid();
            // Each range must be valid
            ret &= start.cmp_end(stop) <= Ordering::Equal;

            // Find the next value immediately after `prev_stop`,
            // or default to the max value if there is none.
            let start_limit = prev_stop.next_after().unwrap_or(T::max_value());

            // The next range must be strictly after start_limit, i.e.,
            // with a gap between the two.  This also handles the case
            // where `start_limit` saturated because `prev_stop` is
            // already at the max value: the comparison is always
            // false, exactly what we want (can't have an interval
            // strictly after one that ends at the max value).
            ret &= start_limit.cmp_end(start) < Ordering::Equal;

            prev_stop = stop;
        }

        ret
    }

    doit(intervals.into_iter())
}

/// Normalizes the slice of intervals in place, in a prefix of the input
/// slice.
///
/// Returns the size of the normalized prefix; remaining elements in
/// the suffix of `intervals` are arbitrary (but were at some point in
/// the original `intervals`).
#[inline(always)]
fn normalize_slice<T: Endpoint>(mut intervals: &mut [(T, T)]) -> usize {
    use std::cmp::Ordering; // Safe because we only use results after validity check

    let first_is_valid = match intervals.first() {
        Some(first) => first.0.is_valid() & first.1.is_valid(),
        None => return 0, // Empty slice is always valid
    };

    let is_sorted = intervals.is_sorted_by(|x, y| {
        x.0.is_valid()
            & x.1.is_valid()
            & y.0.is_valid()
            & y.1.is_valid()
            & (T::cmp_range(*x, *y) <= Ordering::Equal)
    });

    if !(first_is_valid & is_sorted) {
        // Move all valid values to the front.
        let mut valid_prefix_len = 0usize;
        for idx in 0..intervals.len() {
            let cur = intervals[idx];
            intervals[valid_prefix_len] = cur;
            valid_prefix_len += (cur.0.is_valid() & cur.1.is_valid()) as usize;
        }

        intervals = &mut intervals[0..valid_prefix_len];

        // Safe to compare because everything is valid.
        intervals.sort_by(|x, y| T::cmp_range(*x, *y));
    }

    // Once we get here, `intervals` is all valid and sorted, it's safe to compare.
    // The destination is just before the end of the prefix.
    let mut prefix_len = 0usize;
    for idx in 0..intervals.len() {
        assert!(prefix_len <= idx);

        let (cur_start, cur_stop) = intervals[idx];
        // Empty interval. skip
        if cur_start.cmp_end(cur_stop) > Ordering::Equal {
            continue;
        }

        let dst = if prefix_len == 0 {
            intervals[prefix_len] = (cur_start, cur_stop);
            prefix_len = 1;
            0
        } else {
            // prefix_len > 0.
            prefix_len - 1
        };

        assert!(dst <= idx);
        let (acc_start, acc_stop) = intervals[prefix_len - 1];
        debug_assert!(acc_start.cmp_end(acc_stop) <= Ordering::Equal);
        debug_assert!(acc_start.cmp_end(cur_start) <= Ordering::Equal);
        debug_assert!(cur_start.cmp_end(cur_stop) <= Ordering::Equal);
        debug_assert!(acc_start.cmp_end(cur_stop) <= Ordering::Equal);

        let next_start = acc_stop.next_after().unwrap_or(T::max_value());
        if cur_start.cmp_end(next_start) <= Ordering::Equal {
            intervals[dst] = (acc_start, acc_stop.top_end(cur_stop));
        } else {
            debug_assert!(
                !((acc_start.cmp_end(cur_start) <= Ordering::Equal)
                    & (acc_stop.cmp_end(cur_start) >= Ordering::Equal))
            );
            assert!(dst < idx);
            intervals[dst + 1] = (cur_start, cur_stop);
            prefix_len += 1
        }
    }

    debug_assert!(is_normalized(&intervals[0..prefix_len]));

    prefix_len
}

/// Normalizes the vector of intervals and returns a vector that
/// represents the same set of values, without redundancy.
///
/// No-ops quickly when `intervals` is known to be normalized at
/// compile time.
///
/// This operation always operates in place (constant space) and takes
/// constant time when `intervals` is known to be normalized at
/// compile time.
///
/// Barring pre-normalised input, this operation takes linear time
/// when the input is already normalised or otherwise sorted, and
/// \\(\mathcal{O}(n \log n)\\) time in the input size (number of
/// ranges) in the general case.
#[inline(always)]
pub fn normalize_vec<T: Endpoint>(intervals: impl Into<RangeCase<T>>) -> RangeVec<T> {
    #[inline(never)]
    fn doit<T: Endpoint>(mut intervals: Backing<T>) -> RangeVec<T> {
        let remainder = normalize_slice(&mut intervals[..]);
        intervals.truncate(remainder);

        unsafe { RangeVec::new_unchecked(intervals) }
    }

    match intervals.into().unerase() {
        Ok(ret) => ret,
        Err(vec) => doit(vec),
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod test {
    use super::*;
    use crate::Backing;

    #[test]
    fn test_smoke() {
        let mut intervals: [(u8, u8); 7] =
            [(1, 0), (1, 3), (4, 5), (2, 3), (7, 10), (20, 10), (7, 4)];
        for start in 0..intervals.len() - 2 {
            assert!(!is_normalized(&intervals[start..]));
            let v = intervals[start..].to_vec();
            assert!(!is_normalized(&v));
            assert!(!is_normalized(v));
        }

        assert_eq!(normalize_slice(&mut intervals), 2);
        assert_eq!(intervals[..2], [(1, 5), (7, 10)]);

        let mut empty: [(u8, u8); 0] = [];
        assert_eq!(normalize_slice(&mut empty), 0);

        let mut empty: [(u8, u8); 0] = [];
        assert_eq!(normalize_slice(&mut empty), 0);
    }

    #[test]
    fn test_smoke_vec() {
        let intervals: Vec<(u8, u8)> = vec![(1, 3), (3, 5), (2, 3), (7, 10)];
        assert!(!is_normalized(&intervals));

        let normalized_intervals = normalize_vec(intervals);
        assert_eq!(normalized_intervals.inner(), &[(1, 5), (7, 10)]);
        assert_eq!(
            normalized_intervals.clone(),
            normalize_vec(normalized_intervals)
        );

        assert_eq!(normalize_vec(Vec::<(u8, u8)>::new()).into_vec(), vec![]);
    }

    #[test]
    fn test_units() {
        for bits in 0..=u16::MAX {
            let mut atomic_intervals = Backing::<u8>::new();
            for i in (0..16u8).rev() {
                if (bits & (1 << i)) != 0 {
                    atomic_intervals.push((i, i))
                }
            }

            assert!((atomic_intervals.len() <= 1) | (!is_normalized(&atomic_intervals[..])));
            let mut intervals = atomic_intervals;
            intervals = normalize_vec(intervals).into_inner();

            assert!(intervals.is_sorted());

            let mut result: u16 = 0;
            for (left, right) in intervals.iter().copied() {
                assert!(left <= right);
                for i in left..=right {
                    result |= 1 << i;
                }
            }

            assert_eq!(bits, result);

            // Check no overlap or adjacency.
            for ((_, curr_stop), (next_start, _)) in intervals.iter().zip(intervals.iter().skip(1))
            {
                assert!(curr_stop < next_start);
                assert!(next_start - curr_stop > 1);
            }
        }
    }

    #[test]
    fn test_merge_normalized() {
        for bits in 0..=u16::MAX {
            let mut first = Backing::<u8>::new();
            let mut second = Backing::<u8>::new();
            for i in 0..8u8 {
                if bits & (1 << i) != 0 {
                    first.push((i, i))
                }

                if (bits >> 8) & (1 << i) != 0 {
                    second.push((i, i))
                }
            }

            first = normalize_vec(first).into_inner();
            second = normalize_vec(second).into_inner();

            let mut intervals = first;
            intervals.extend(second);

            intervals = normalize_vec(intervals).into_inner();
            assert!(intervals.is_sorted());

            let mut result: u16 = 0;
            for (left, right) in intervals.iter().copied() {
                assert!(left <= right);
                for i in left..=right {
                    result |= 1 << i;
                }
            }

            assert_eq!((bits & 255) | (bits >> 8), result);

            // Check no overlap or adjacency.
            for ((_, curr_stop), (next_start, _)) in intervals.iter().zip(intervals.iter().skip(1))
            {
                assert!(curr_stop < next_start);
                assert!(next_start - curr_stop > 1);
            }
        }
    }

    #[test]
    fn test_merge_few_ranges() {
        fn ranges_to_bits(entries: &[(u8, u8)]) -> u128 {
            let mut ret = 0u128;

            for (start, stop) in entries.iter().copied() {
                assert!(start < 128);
                assert!(stop < 128);

                if start <= stop {
                    for bit in start..=stop {
                        ret |= 1u128 << bit;
                    }
                }
            }

            ret
        }

        fn test(entries: &[(u8, u8)]) {
            let initial_bits = ranges_to_bits(entries);
            let normalized = normalize_vec(entries.to_vec());
            assert_eq!(initial_bits, ranges_to_bits(normalized.inner()));
        }

        for start_0 in 0..=10 {
            for stop_0 in 0..=10 {
                for start_1 in 0..=10 {
                    for stop_1 in 0..=10 {
                        for start_2 in 0..=10 {
                            for stop_2 in 0..=10 {
                                test(&[(start_0, stop_0), (start_1, stop_1), (start_2, stop_2)])
                            }
                        }
                    }
                }
            }
        }
    }

    // nans and such
    #[test]
    fn test_fp_limits() {
        // NaN
        assert!(!is_normalized([(f32::NAN, f32::NAN)]));
        assert!(!is_normalized([(0.0, f32::NAN)]));
        assert!(!is_normalized([(f64::NAN, 0.0)]));
        assert!(!is_normalized([
            (0.0, 1.0),
            (f32::NAN, f32::NAN),
            (2.0, 3.0)
        ]));
        assert!(!is_normalized([(0.0, 1.0), (f64::NAN, 10.0), (12.0, 13.0)]));
        assert!(!is_normalized([(0.0, 1.0), (10.0, f64::NAN), (12.0, 13.0)]));
        assert!(!is_normalized([(0.0, 1.0), (f64::NAN, 10.0)]));
        assert!(!is_normalized([(0.0, 1.0), (10.0, f64::NAN)]));

        // Also check NaN handling in `normalize`.
        {
            let norm = RangeVec::from_vec(vec![(f64::NAN, f64::NAN)]);
            assert!(norm.is_empty());

            let norm = RangeVec::from_vec(vec![(0.0, f64::NAN)]);
            assert!(norm.is_empty());

            let norm = RangeVec::from_vec(vec![(f64::NAN, 0.0)]);
            assert!(norm.is_empty());
        }

        {
            let norm = RangeVec::from_vec(vec![
                (0.0, 1.0),
                (f32::NAN, f32::NAN),
                (2.0, 3.0),
                (f32::NAN, 2.0),
                (1.0, f32::NAN),
            ]);
            assert_eq!(norm.inner(), &[(0.0, 1.0), (2.0, 3.0)]);
        }

        // Signed zeros
        assert!(!is_normalized([(0.0f64, -0.0f64)]));
        assert!(is_normalized([(-0.0f64, 0.0f64)]));
        assert!(is_normalized([(-0.0f64, -0.0f64)]));
        assert!(is_normalized([(0.0f32, 0.0f32)]));

        // Too close
        assert!(!is_normalized([(-0.0f32, -0.0f32), (0.0f32, 0.0f32)]));
        assert!(!is_normalized([(0.0, 0.0), (-0.0, 0.0)]));
        assert!(!is_normalized([(0.0, 0.0), (-0.0, -0.0)]));

        // Some infinities
        assert!(!is_normalized([
            (f32::NEG_INFINITY, -0.0f32), // too close
            (0.0f32, f32::INFINITY)
        ]));
        assert!(is_normalized([
            (f32::NEG_INFINITY, f32::NEG_INFINITY),
            (0f32, f32::INFINITY)
        ]));
        // f64::MAX and f64::INFINITY are too close.
        assert!(!is_normalized([
            (f64::NEG_INFINITY, f64::MAX),
            (f64::INFINITY, f64::INFINITY)
        ]));
    }

    proptest::proptest! {
        #[test]
        fn is_normalized_negative(x: (u8, u8), y: (u8, u8), ranges: Vec<(u8, u8)>) {
            let mut ranges = ranges;
            ranges.push(x);
            ranges.push(y);

            // They can't both be right.
            let ltr = is_normalized(&ranges);

            ranges.reverse();
            let rtl = is_normalized(&ranges);

            assert!(!(ltr & rtl));
        }

        #[test]
        fn is_normalized_positive(ranges: Vec<(u8, u8)>) {
            let mut marks = vec![false; 256];

            for (x, y) in ranges {
                let (lo, hi) = (x.min(y), x.max(y));

                for i in lo..=hi {
                    marks[i as usize] = true;
                }
            }

            let mut normalized_ranges = Vec::new();

            for i in 0..marks.len() {
                if !marks[i] {
                    continue;
                }

                if i == 0 || !marks[i - 1] {
                    normalized_ranges.push((i as u8, i as u8));
                } else {
                    normalized_ranges.last_mut().unwrap().1 = i as u8;
                }
            }

            assert!(is_normalized(&normalized_ranges));

            if !normalized_ranges.is_empty() {
                normalized_ranges.push((0u8, 255u8));
                assert!(!is_normalized(&normalized_ranges));
                normalized_ranges.pop();
            }

            if normalized_ranges.len() > 1 {
                normalized_ranges.reverse();
                assert!(!is_normalized(&normalized_ranges));
                normalized_ranges.reverse();

                let first = normalized_ranges[0];
                let last = *normalized_ranges.last().unwrap();

                normalized_ranges[0] = last;
                *normalized_ranges.last_mut().unwrap() = first;

                assert!(!is_normalized(&normalized_ranges));
            }
        }

        #[test]
        fn test_normalize_vec(ranges: Vec<(u8, u8)>) {
            use crate::ranges_to_bits;

            let initial_marks = ranges_to_bits(&ranges);
            let normalized = normalize_vec(ranges.clone());

            // Normalizing a RangeVec should no-op.
            let clone = normalized.clone();
            let clone_ptr = clone.as_ptr() as usize;
            let double_normalized = normalize_vec(clone);
            // This doesn't test as much you'd think because even full
            // normalization is in-place.
            if double_normalized.len() > crate::INLINE_SIZE {
                assert_eq!(clone_ptr, double_normalized.as_ptr() as usize);
            }

            assert_eq!(&normalized, &double_normalized);

            assert_eq!(&initial_marks, &ranges_to_bits(&normalized));
            assert_eq!(&initial_marks, &ranges_to_bits(&double_normalized));

            assert_eq!(&normalized, &RangeVec::from_vec(ranges));
            assert_eq!(&normalized, &RangeVec::from_smallvec(double_normalized.clone().into_inner()));
            assert_eq!(&normalized, &RangeVec::from_vec(double_normalized.into_vec()));
        }

        #[test]
        fn test_smoke_is_normalized_vec_f32(mut ranges: Vec<(f32, f32)>) {
            let ltr = is_normalized(&ranges);
            ranges.reverse();
            let rtl = is_normalized(&ranges);

            if ranges.is_empty() {
                assert!(ltr);
                assert!(rtl);
            } else {
                let first = ranges[0];
                if ranges
                    .iter()
                    .all(|x| f32::cmp_range(*x, first) == std::cmp::Ordering::Equal)
                {
                    assert_eq!(ltr, rtl);
                } else {
                    // They can't both be correct
                    assert!(!ltr || !rtl);
                }
            }
        }

        #[test]
        fn test_smoke_normalize_vec_f64(ranges: Vec<(f64, f64)>) {
            let normalized = normalize_vec(ranges.clone());

            // Normalizing a RangeVec should no-op.
            let clone = normalized.clone();
            let clone_ptr = clone.as_ptr() as usize;
            let double_normalized = normalize_vec(clone);
            // This doesn't test as much you'd think because even full
            // normalization is in-place.
            if double_normalized.len() > crate::INLINE_SIZE {
                assert_eq!(clone_ptr, double_normalized.as_ptr() as usize);
            }
            assert_eq!(&normalized, &double_normalized);

            assert_eq!(&normalized, &RangeVec::from_vec(ranges));
            assert_eq!(
                &normalized,
                &RangeVec::from_smallvec(double_normalized.into_inner())
            );
        }
    }
}
