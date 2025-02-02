//! While most operations work on (branded) iterators, some need
//! restricted random access.  These random-access operations are
//! defined in this module.
use crate::Endpoint;
use crate::Pair;

/// A [`Sequence`] can be consumed forward, like a copyable iterator.
///
/// However, we also assume the contents are sorted, and use this to
/// skip ahead, with `skip_to`.
pub trait Sequence: Copy {
    /// The endpoint type for the ranges (pairs of endpoints)
    /// contained in the sequence.
    type EndT: Endpoint;

    /// If self is empty, returns [`None`].  Otherwise, returns the
    /// first element and the remainder of the sequence.
    fn uncons(self) -> Option<(Pair<Self::EndT>, Self)>;

    /// Skips all but one value in `self` that is less than `x`,
    /// given `cursor`, a special suffix of `self`.
    ///
    /// If some element (e.g., the first) of `self` is less than `x`:
    ///
    ///   Returns a suffix of `self` such that the first element in the
    ///   return value is less than `x` and the next, if any, is greater
    ///   than or equal to `x`.
    ///
    ///   The `cursor` must be a suffix of `self` such that the cursor's
    ///   first element is less than `x`.
    ///
    /// If `self` is empty or its elements are all greater than or equal to `x`:
    ///
    ///   Returns self.  The `cursor` must be `self`.
    ///
    /// In all cases, it is safe to use the return value of `skip_to` as
    /// the cursor for a subsequence call to `skip_to`, as long as the
    /// `x` arguments are monotonically non-decreasing.  It is also always
    /// safe to pass `self` as the `cursor`.
    fn skip_to(self, x: Pair<Self::EndT>, cursor: Self) -> Self;
}

#[inline(always)]
fn compute_linear_work_factor(len: usize) -> usize {
    const MIN_LINEAR_WORK: usize = 8;
    const LINEAR_WORK_MASK: usize = (1usize << (1 + MIN_LINEAR_WORK / 2)) - 1;
    const _: () = assert!(LINEAR_WORK_MASK.count_ones() as usize == 1 + MIN_LINEAR_WORK / 2);

    2 * (len | LINEAR_WORK_MASK).ilog2() as usize
}

impl<'a, T: 'a + Endpoint> Sequence for &'a [(T, T)] {
    type EndT = T;

    #[inline(always)]
    fn uncons(self) -> Option<((T, T), Self)> {
        let head = self.first()?;

        Some((*head, &self[1..]))
    }

    /// Implement `skip_to` with a bounded linear search from the
    /// cursor, followed by a binary search when out of search budget.
    #[inline(never)]
    fn skip_to(self, x: (T, T), cursor: Self) -> Self {
        let doit = || {
            let linear_work_factor = compute_linear_work_factor(self.len());
            skip_to_linear_search(cursor, x, linear_work_factor)
                .unwrap_or_else(|| skip_to_binary_search(self, x))
        };

        #[cfg(debug_assertions)]
        slice_skip_to_preconditions(self, x, cursor);

        let ret = doit();

        #[cfg(debug_assertions)]
        slice_skip_to_guarantees(ret, self, x);

        ret
    }
}

#[allow(dead_code)]
#[inline(always)]
fn slice_skip_to_preconditions<T: Copy + Ord>(this: &[T], x: T, cursor: &[T]) {
    // `Sequence`s must be sorted
    assert!(this.is_sorted());
    assert!(cursor.is_sorted());
    // in fact, cursor is a suffix of this.
    assert!(this.len() >= cursor.len());
    assert!(std::ptr::eq(&this[this.len() - cursor.len()..], cursor));

    if let Some(first) = this.first().copied() {
        // There is some element of `this` less than x.
        if first < x {
            let cursor_first = cursor
                .first()
                .expect("cursor must start at value less than x");
            assert!(*cursor_first < x);
        } else {
            // x is too small, we're in the second behaviour,
            // and `cursor` must be equal to this.
            assert!(this.len() == cursor.len());
            assert!(std::ptr::eq(this, cursor));
        }
    } else {
        // If `this` is empty, we're in the second behaviour.
        assert!(cursor.is_empty());
    }
}

#[allow(dead_code)]
#[inline(always)]
fn slice_skip_to_guarantees<T: Copy + Ord>(ret: &[T], this: &[T], x: T) {
    // The return value is a suffix of `this`.
    assert!(ret.len() <= this.len());
    assert!(std::ptr::eq(ret, &this[this.len() - ret.len()..]));

    match this.first().copied() {
        // If we initially had a first value less than x...
        Some(first) if first < x => {
            assert!(ret.first().copied().expect("should have initial value") < x);
            // The next value, if any, should be greater than or equal to x.
            if let Some(next) = ret.get(1) {
                assert!(*next >= x);
            }
        }
        _ => {
            // x was too small, we just return this.
            assert!(std::ptr::eq(ret, this));
        }
    }
}

#[inline(always)]
fn skip_to_linear_search<T: Copy + Ord>(
    cursor: &[T],
    needle: T,
    linear_work_factor: usize,
) -> Option<&[T]> {
    for (idx, y) in cursor.iter().skip(1).enumerate().take(linear_work_factor) {
        if *y >= needle {
            return Some(&cursor[idx..]);
        }
    }

    None
}

#[inline(always)]
fn skip_to_binary_search<T: Copy + Ord>(haystack: &[T], needle: T) -> &[T] {
    let idx = haystack.partition_point(|x| *x < needle);
    &haystack[idx.saturating_sub(1)..]
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod test {
    use super::*;

    #[test]
    fn test_skip_to_slices_subsearch() {
        let mut sequence: Vec<u8> = Vec::with_capacity(200);
        sequence.extend([4, 5, 6, 7]);
        for i in (1..32).step_by(2) {
            sequence.push(i + 1);
            // Sprinkle some dups
            if i < 5 || (10..15).contains(&i) || i > 25 {
                sequence.push(i + 1);
            }
        }

        sequence.sort();
        assert!(sequence[0] > 0);
        assert!(*sequence.last().unwrap() < 100);

        let sequence: &[u8] = &sequence;
        for needle in 0..=255u8 {
            let hit = skip_to_binary_search(sequence, needle);
            slice_skip_to_guarantees(hit, sequence, needle);

            // Make sure `hit` is a suffix of `sequence`.
            assert!(hit.len() <= sequence.len());
            assert_eq!(hit, &sequence[sequence.len() - hit.len()..]);
            assert!(std::ptr::eq(hit, &sequence[sequence.len() - hit.len()..]));

            if needle <= sequence[0] {
                assert_eq!(hit, sequence);
            } else if needle > *sequence.last().unwrap() {
                assert_eq!(hit, &[*sequence.last().unwrap()]);
            } else {
                // We know there's one element less than needle, and one
                // greater than or equal, the return value must have at
                // least two entries.
                assert!(*hit.first().unwrap() < needle);
                assert!(*hit.get(1).unwrap() >= needle);
            }

            // Now make sure the linear search returns the same thing.
            if let Some(linear_hit) = skip_to_linear_search(sequence, needle, usize::MAX) {
                assert_eq!(hit, linear_hit);
                assert!(std::ptr::eq(hit, linear_hit));
            } else {
                // If the linear search failed, that's because it got to the end.
                assert_eq!(hit, &[*sequence.last().unwrap()]);
            }
        }
    }

    #[test]
    fn test_uncons() {
        let sequence = [(1u8, 2u8), (10u8, 20u8)];

        let mut sequence = &sequence[..];
        {
            let head;

            (head, sequence) = sequence.uncons().expect("non-empty");
            assert_eq!(head, (1, 2));
        }

        {
            let head;

            (head, sequence) = sequence.uncons().expect("non-empty");
            assert_eq!(head, (10, 20));
        }

        assert_eq!(sequence.uncons(), None);
    }

    #[test]
    fn test_skip_to_slices() {
        let mut sequence: Vec<(u8, u8)> = Vec::with_capacity(200);
        sequence.extend([4, 5, 6, 7].map(|x| (x, x)));
        for i in (1..32).step_by(2) {
            sequence.push((i + 1, i + 1));
            // Sprinkle some dups
            if i < 5 || (10..15).contains(&i) || i > 25 {
                sequence.push((i + 1, i + 1));
            }
        }

        sequence.sort();
        assert!(sequence[0] > (0, 0));
        assert!(*sequence.last().unwrap() < (100, 100));

        let sequence: &[(u8, u8)] = &sequence;
        let mut cursor = sequence;
        for needle in (0..=255u8).map(|x| (x, x)) {
            let hit = sequence.skip_to(needle, cursor);

            // Make sure `hit` is a suffix of `sequence`.
            assert!(hit.len() <= sequence.len());
            assert_eq!(hit, &sequence[sequence.len() - hit.len()..]);
            assert!(std::ptr::eq(hit, &sequence[sequence.len() - hit.len()..]));

            // `hit` should be a suffix of `cursor`
            assert!(hit.len() <= cursor.len());
            assert_eq!(hit, &cursor[cursor.len() - hit.len()..]);
            assert!(std::ptr::eq(hit, &cursor[cursor.len() - hit.len()..]));

            cursor = hit;
            if needle <= sequence[0] {
                assert_eq!(hit, sequence);
            } else if needle > *sequence.last().unwrap() {
                assert_eq!(hit, &[*sequence.last().unwrap()]);
            } else {
                // We know there's one element less than needle, and one
                // greater than or equal, the return value must have at
                // least two entries.
                assert!(*hit.first().unwrap() < needle);
                assert!(*hit.get(1).unwrap() >= needle);
            }

            // We should get the same result for all prefixes of `cursor`.
            for cursor_start in 0..sequence.len() {
                let prefix = &sequence[cursor_start..];
                let other_hit = sequence.skip_to(needle, prefix);
                assert_eq!(hit, other_hit);
                assert!(std::ptr::eq(hit, other_hit));

                if std::ptr::eq(prefix, cursor) {
                    break;
                }
            }
        }
    }

    #[test]
    fn test_skip_to_slices_empty() {
        let sequence: &[(u8, u8)] = &[];

        for needle in (0..=255u8).map(|x| (x, x)) {
            assert_eq!(skip_to_linear_search(sequence, needle, usize::MAX), None);
            assert_eq!(skip_to_binary_search(sequence, needle), sequence);
            assert_eq!(sequence.skip_to(needle, sequence), sequence);
        }
    }

    #[test]
    fn test_work_factor() {
        assert_eq!(compute_linear_work_factor(0), 8);
        for i in 0..32 {
            assert_eq!(compute_linear_work_factor(i), 8);
        }

        assert_eq!(compute_linear_work_factor(32), 10);
        assert_eq!(compute_linear_work_factor(33), 10);
        assert_eq!(compute_linear_work_factor(256), 16);
        assert_eq!(compute_linear_work_factor(512), 18);
        assert_eq!(compute_linear_work_factor(usize::MAX), 126);
    }
}
