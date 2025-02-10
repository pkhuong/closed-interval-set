use crate::Backing;
use crate::ClosedRange;
use crate::Endpoint;
use crate::RangeCase;
use crate::RangeVec;

/// Computes the normalized union of `acc` and `src`.
///
/// There's no particularly smart way to do this (except maybe with a
/// sorted merge, but hopefully the default [`slice::sort`] handles
/// sorted runs): concatenate everything and normalize in place.
///
/// This operation reuses the storage from `acc` and takes
/// \\(\mathcal{O}(n \log n)\\) time, where \\(n\\) is the total
/// number of ranges in the two inputs.
#[inline]
pub fn union_vec<T: Endpoint>(
    acc: impl Into<RangeCase<T>>,
    src: impl IntoIterator<Item: ClosedRange<EndT = T>>,
) -> RangeVec<T> {
    fn doit<T: Endpoint>(
        mut acc: Backing<T>,
        src: impl Iterator<Item: ClosedRange<EndT = T>>,
    ) -> RangeVec<T> {
        acc.extend(src.map(|range| range.get()));
        crate::normalize_vec(acc)
    }

    doit(acc.into().into_inner(), src.into_iter())
}

impl<T: Endpoint> RangeVec<T> {
    /// Constructs the union of this [`RangeVec`] and any of a
    /// [`RangeVec`], a [`SmallVec`], or a [`Vec`].
    ///
    /// This operation reuses the storage from `self` and takes
    /// \\(\mathcal{O}(n \log n)\\) time, where \\(n\\) is the total
    /// size of the two inputs. This is worse than the linear-time
    /// [`RangeVec::union`], but the constant factors are pretty good.
    ///
    /// See [`union_vec`] for more general types.
    ///
    /// [`SmallVec`]: https://docs.rs/smallvec/latest/smallvec/struct.SmallVec.html
    /// [`Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
    #[inline(always)]
    pub fn into_union(self, other: impl Into<RangeCase<T>>) -> Self {
        #[cfg(feature = "internal_checks")]
        use crate::NormalizedRangeIter;

        fn doit<T: Endpoint>(mut x: Backing<T>, mut y: Backing<T>) -> RangeVec<T> {
            if y.len() > x.len() {
                core::mem::swap(&mut x, &mut y);
            }

            // More efficient when the first argument is longer
            debug_assert!(x.len() >= y.len());
            union_vec(x, y)
        }

        let other = other.into().into_inner();

        #[cfg(feature = "internal_checks")]
        let expected = (
            self.iter()
                .union(RangeVec::from_smallvec(other.clone()))
                .collect_range_vec(),
            RangeVec::from_smallvec(other.clone())
                .iter()
                .union(self.iter())
                .collect_range_vec(),
        );

        let ret = doit(self.into_inner(), other);

        #[cfg(feature = "internal_checks")]
        {
            assert!(expected.0.eqv(&ret));
            assert!(expected.1.eqv(&ret));
        }

        ret
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod test {
    use super::*;
    use alloc::vec;
    use alloc::vec::Vec;

    #[test]
    fn test_union_smoke() {
        use crate::NormalizedRangeIter;

        let acc = vec![(1u8, 4u8), (5u8, 1u8), (5u8, 10u8)];
        let src = [(0u8, 2u8), (11u8, 15u8)];

        assert_eq!(
            crate::normalize_vec(acc.clone())
                .into_union(src.to_vec())
                .into_vec(),
            vec![(0u8, 15u8)]
        );

        assert_eq!(
            crate::normalize_vec(src.to_vec())
                .union(crate::normalize_vec(vec![]))
                .into_vec(),
            src.to_vec()
        );

        let result = union_vec(acc, src);
        assert_eq!(&*result, &vec![(0u8, 15u8)]);
        assert_eq!(result.inner(), &vec![(0u8, 15u8)]);
        assert_eq!(result.iter().collect::<Vec<_>>(), vec![(0u8, 15u8)]);
        assert_eq!(
            result.iter().collect_range_vec().into_vec(),
            vec![(0u8, 15u8)]
        );
        assert_eq!(result.into_vec(), vec![(0u8, 15u8)]);
    }

    proptest::proptest! {
        #[test]
        fn test_union(xs: Vec<(u8, u8)>, ys: Vec<(u8, u8)>)
        {
            use crate::ranges_to_bits;

            let bits = {
                let mut all_ranges = xs.clone();
                all_ranges.extend(&ys);
                ranges_to_bits(&all_ranges)
            };

            // union_vec
            {
                let union = union_vec(xs.clone(), &ys);
                assert_eq!(bits, ranges_to_bits(&union));
            }

            {
                let union = union_vec(RangeVec::from_vec(xs.clone()), &ys);
                assert_eq!(bits, ranges_to_bits(&union));
            }

            {
                let union = union_vec(xs.clone(), RangeVec::from_vec(ys.clone()).iter());
                assert_eq!(bits, ranges_to_bits(&union));
            }

            {
                let union = union_vec(RangeVec::from_vec(xs.clone()), RangeVec::from_vec(ys.clone()).iter());
                assert_eq!(bits, ranges_to_bits(&union));
            }

            // union
            {
                let union = RangeVec::from_vec(xs.clone()).into_union(ys.clone());
                assert_eq!(bits, ranges_to_bits(&union));
            }

            {
                let union = RangeVec::from_vec(ys.clone()).union(RangeVec::from_vec(xs.clone()));
                assert_eq!(bits, ranges_to_bits(&union));
            }
        }
    }
}
