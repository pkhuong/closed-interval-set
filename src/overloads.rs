use crate::ClosedRange;
use crate::Endpoint;
use crate::NormalizedRangeIter;
use crate::RangeVec;

use alloc::boxed::Box;

impl<T: Endpoint> core::ops::BitAnd<&RangeVec<T>> for &RangeVec<T> {
    type Output = RangeVec<T>;

    fn bitand(self, rhs: &RangeVec<T>) -> RangeVec<T> {
        crate::intersect_vec(self, rhs)
    }
}

impl<T: Endpoint> core::ops::BitAndAssign<&RangeVec<T>> for RangeVec<T> {
    fn bitand_assign(&mut self, rhs: &RangeVec<T>) {
        let mut tmp = RangeVec::new();
        core::mem::swap(&mut tmp, self);
        *self = &tmp & rhs;
    }
}

impl<T: Endpoint> core::ops::BitAnd<RangeVec<T>> for &RangeVec<T> {
    type Output = RangeVec<T>;

    fn bitand(self, rhs: RangeVec<T>) -> RangeVec<T> {
        self & &rhs
    }
}

impl<T: Endpoint> core::ops::BitAndAssign<RangeVec<T>> for RangeVec<T> {
    fn bitand_assign(&mut self, rhs: RangeVec<T>) {
        *self &= &rhs;
    }
}

impl<T: Endpoint> core::ops::BitOr<RangeVec<T>> for RangeVec<T> {
    type Output = RangeVec<T>;

    fn bitor(mut self, mut rhs: RangeVec<T>) -> RangeVec<T> {
        if self.len() < rhs.len() {
            core::mem::swap(&mut self, &mut rhs);
        }

        self.into_union(rhs)
    }
}

impl<T: Endpoint> core::ops::BitOrAssign<RangeVec<T>> for RangeVec<T> {
    fn bitor_assign(&mut self, rhs: RangeVec<T>) {
        let mut tmp = RangeVec::new();
        core::mem::swap(&mut tmp, self);
        *self = tmp | rhs;
    }
}

impl<T: Endpoint> core::ops::BitOr<&RangeVec<T>> for RangeVec<T> {
    type Output = RangeVec<T>;

    fn bitor(self, rhs: &RangeVec<T>) -> RangeVec<T> {
        crate::union_vec(self, rhs)
    }
}

impl<T: Endpoint> core::ops::BitOrAssign<&RangeVec<T>> for RangeVec<T> {
    fn bitor_assign(&mut self, rhs: &RangeVec<T>) {
        let mut tmp = RangeVec::new();
        core::mem::swap(&mut tmp, self);
        *self = tmp | rhs;
    }
}

impl<T: Endpoint> core::ops::BitOr<&RangeVec<T>> for &RangeVec<T> {
    type Output = RangeVec<T>;

    fn bitor(self, rhs: &RangeVec<T>) -> RangeVec<T> {
        self.union(rhs)
    }
}

impl<T: Endpoint> core::ops::Not for &RangeVec<T> {
    type Output = RangeVec<T>;

    fn not(self) -> RangeVec<T> {
        self.complement()
    }
}

impl<T: Endpoint> core::ops::Not for RangeVec<T> {
    type Output = RangeVec<T>;

    fn not(self) -> RangeVec<T> {
        crate::complement_vec(self)
    }
}

impl<
        T: 'static + Endpoint,
        X: 'static + ClosedRange<EndT = T>,
        Y: 'static + ClosedRange<EndT = T>,
    > core::ops::BitAnd<Box<dyn NormalizedRangeIter<Item = Y>>>
    for Box<dyn NormalizedRangeIter<Item = X>>
{
    type Output = Box<dyn NormalizedRangeIter<Item = (T, T)>>;

    fn bitand(self, rhs: Box<dyn NormalizedRangeIter<Item = Y>>) -> Self::Output {
        Box::new(self.intersect(rhs))
    }
}

impl<
        T: 'static + Endpoint,
        X: 'static + ClosedRange<EndT = T>,
        Y: 'static + ClosedRange<EndT = T>,
    > core::ops::BitOr<Box<dyn NormalizedRangeIter<Item = Y>>>
    for Box<dyn NormalizedRangeIter<Item = X>>
{
    type Output = Box<dyn NormalizedRangeIter<Item = (T, T)>>;

    fn bitor(self, rhs: Box<dyn NormalizedRangeIter<Item = Y>>) -> Self::Output {
        Box::new(self.union(rhs))
    }
}

impl<T: Endpoint + 'static, X: 'static + ClosedRange<EndT = T>> core::ops::Not
    for Box<dyn NormalizedRangeIter<Item = X>>
{
    type Output = Box<dyn NormalizedRangeIter<Item = (T, T)>>;

    fn not(self) -> Self::Output {
        Box::new(self.complement())
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod test {
    use super::*;

    #[test]
    fn smoke_test_ref_vec_ops() {
        let mut x = RangeVec::from_vec(vec![(1u8, 4u8), (10u8, 12u8)]);
        let y = RangeVec::from_vec(vec![(2u8, 6u8), (11u8, 11u8)]);

        assert_eq!(&x & &y, RangeVec::from_vec(vec![(2u8, 4u8), (11u8, 11u8)]));
        assert_eq!(
            &x & y.clone(),
            RangeVec::from_vec(vec![(2u8, 4u8), (11u8, 11u8)])
        );
        assert_eq!(&x | &y, RangeVec::from_vec(vec![(1u8, 6u8), (10u8, 12u8)]));
        assert_eq!(
            !&x,
            RangeVec::from_vec(vec![(0u8, 0u8), (5u8, 9u8), (13u8, 255u8)])
        );

        x &= y;
        assert_eq!(x, RangeVec::from_vec(vec![(2u8, 4u8), (11u8, 11u8)]));
    }

    #[test]
    fn smoke_test_vec_ops() {
        let mut x = RangeVec::from_vec(vec![(1u8, 4u8), (10u8, 12u8)]);
        let y = RangeVec::from_vec(vec![(2u8, 6u8), (11u8, 11u8), (255u8, 255u8)]);

        assert_eq!(
            x.clone() | y.clone(),
            RangeVec::from_vec(vec![(1u8, 6u8), (10u8, 12u8), (255u8, 255u8)])
        );
        assert_eq!(
            x.clone() | &y,
            RangeVec::from_vec(vec![(1u8, 6u8), (10u8, 12u8), (255u8, 255u8)])
        );
        assert_eq!(
            !x.clone(),
            RangeVec::from_vec(vec![(0u8, 0u8), (5u8, 9u8), (13u8, 255u8)])
        );

        x |= &y;
        assert_eq!(
            x,
            RangeVec::from_vec(vec![(1u8, 6u8), (10u8, 12u8), (255u8, 255u8)])
        );

        x &= !&y;
        assert_eq!(
            x,
            RangeVec::from_vec(vec![(1u8, 1u8), (10u8, 10u8), (12u8, 12u8)])
        );

        x |= y.clone();
        assert_eq!(
            x,
            RangeVec::from_vec(vec![(1u8, 6u8), (10u8, 12u8), (255u8, 255u8)])
        );

        x &= !y;
        assert_eq!(
            x,
            RangeVec::from_vec(vec![(1u8, 1u8), (10u8, 10u8), (12u8, 12u8)])
        );
    }

    #[test]
    fn smoke_test_iterator_ops() {
        let x = RangeVec::from_vec(vec![(1u8, 4u8), (10u8, 12u8)]);
        let y = RangeVec::from_vec(vec![(2u8, 6u8), (11u8, 11u8)]);

        {
            let mut x: Box<dyn NormalizedRangeIter<Item = _>> = Box::new(x.clone().into_iter());
            let y: Box<dyn NormalizedRangeIter<Item = _>> = Box::new(y.clone().into_iter());

            x = x & y;
            assert_eq!(
                RangeVec::from_iter(x),
                RangeVec::from_vec(vec![(2u8, 4u8), (11u8, 11u8)])
            );
        }

        {
            let mut x: Box<dyn NormalizedRangeIter<Item = _>> = Box::new(x.clone().into_iter());
            let y: Box<dyn NormalizedRangeIter<Item = _>> = Box::new(y.clone().into_iter());

            x = x | y;
            assert_eq!(
                RangeVec::from_iter(x),
                RangeVec::from_vec(vec![(1u8, 6u8), (10u8, 12u8)])
            );
        }

        {
            let mut x: Box<dyn NormalizedRangeIter<Item = _>> = Box::new(x.into_iter());
            x = !x;
            assert_eq!(
                RangeVec::from_iter(x),
                RangeVec::from_vec(vec![(0u8, 0u8), (5u8, 9u8), (13u8, 255u8)])
            );
        }
    }
}
