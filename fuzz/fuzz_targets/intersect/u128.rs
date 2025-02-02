#![no_main]

use closed_interval_set::complement_vec;
use closed_interval_set::intersect_vec;
use closed_interval_set::is_normalized;
use closed_interval_set::union_vec;
use closed_interval_set::RangeVec;

use libfuzzer_sys::fuzz_target;

// for SIGN in i u; do for W in 8 16 32 64 128; do cp template.rs $SIGN$W.rs; sed -i -re "s/type T = [ui][0-9]+;/type T = $SIGN$W;/" $SIGN$W.rs; done; done

type T = u128;

// x & y == y & x
//
// -x & -y == -(x | y)
fn check(x: Vec<(T, T)>, y: Vec<(T, T)>) {
    use closed_interval_set::NormalizedRangeIter;

    let x = RangeVec::from_vec(x);
    let y = RangeVec::from_vec(y);

    // Intersection with empty set yields the empty set
    {
        let empty = RangeVec::from_vec(Vec::<(T, T)>::new());

        assert!(intersect_vec(&x, &empty).is_empty());
        assert!(x
            .iter()
            .intersect_vec(&empty)
            .collect_range_vec()
            .is_empty());
        assert!(empty
            .iter()
            .intersect_vec(&y)
            .collect_range_vec()
            .is_empty());
    }

    // Intersection with universe is the identity
    {
        let universe = RangeVec::from_vec(vec![(T::MIN, T::MAX)]);

        assert_eq!(&intersect_vec(&x, &universe), &x);
        assert_eq!(&x.iter().intersect_vec(&universe).collect_range_vec(), &x);
        assert_eq!(&universe.iter().intersect_vec(&y).collect_range_vec(), &y);
    }

    // Check commutativity
    {
        let inter_1 = intersect_vec(&x, &y);
        let inter_2 = x.iter().intersect_vec(&y).collect_range_vec();
        let inter_3 = y.iter().intersect_vec(&x).collect_range_vec();

        assert!(is_normalized(&inter_1));
        assert!(is_normalized(&inter_2));
        assert!(is_normalized(&inter_3));
        assert_eq!(inter_1, inter_2);
        assert_eq!(inter_1, inter_3);
    }

    {
        // -x & -y
        let left = x
            .iter()
            .complement()
            .intersect_vec(&complement_vec(y.clone()))
            .collect_range_vec();
        // -(x | u)
        let right = union_vec(x.clone(), &y).into_complement();
        assert!(is_normalized(&left));
        assert!(is_normalized(&right));
        assert_eq!(left, right);
    }

    {
        // - (x & y)
        let left = y.intersect(&x).complement();
        // (-x | -y)
        let right = x.complement().union(y.complement());

        assert!(is_normalized(&left));
        assert!(is_normalized(&right));
        assert_eq!(left, right);
    }
}

fuzz_target!(|x_y: (Vec<(T, T)>, Vec<(T, T)>)| {
    let (x, y) = x_y;
    check(x.clone(), y.clone());
    let x = x
        .into_iter()
        .map(|(a, b)| (a.min(b), a.max(b)))
        .collect::<Vec<_>>();
    let y = y
        .into_iter()
        .map(|(a, b)| (a.min(b), a.max(b)))
        .collect::<Vec<_>>();
    check(y, x);
});
