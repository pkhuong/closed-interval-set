#![no_main]

use closed_interval_set::is_normalized;
use closed_interval_set::RangeVec;

use libfuzzer_sys::fuzz_target;

// for SIGN in i u; do for W in 8 16 32 64 128; do cp template.rs $SIGN$W.rs; sed -i -re "s/type T = [ui][0-9]+;/type T = $SIGN$W;/" $SIGN$W.rs; done; done

type T = i32;

fn check_single(x: Vec<(T, T)>) {
    use closed_interval_set::NormalizedRangeIter;

    let x = RangeVec::from_vec(x);

    // x | emptyset = x
    {
        let empty = RangeVec::from_vec(Vec::<(T, T)>::new());
        assert_eq!(&x.iter().union(empty.iter()).collect_range_vec(), &x);
        assert_eq!(&empty.iter().union(x.iter()).collect_range_vec(), &x);
    }

    // x | universe = universe
    {
        let universe = RangeVec::from_vec(vec![(T::MIN, T::MAX)]);
        assert_eq!(
            &x.iter().union(universe.iter()).collect_range_vec(),
            &universe
        );
        assert_eq!(
            &universe.iter().union(x.iter()).collect_range_vec(),
            &universe
        );
    }

    // x | x = x
    {
        let double = x.iter().union(x.iter()).collect_range_vec();

        assert_eq!(&x, &double);
    }

    // x | -x = universe
    {
        let universe = x.iter().union(x.iter().complement()).collect_range_vec();

        assert_eq!(universe.inner(), &[(T::MIN, T::MAX)]);
    }
}

// union of iterators == into_union
fn check(x: Vec<(T, T)>, y: Vec<(T, T)>) {
    use closed_interval_set::NormalizedRangeIter;

    let x = RangeVec::from_vec(x);
    let y = RangeVec::from_vec(y);

    // check for commutativity
    let union_iter_1 = x.iter().union(y.iter()).collect_range_vec();
    let union_iter_2 = y.iter().union(x.iter()).collect_range_vec();

    assert_eq!(&union_iter_1, &union_iter_2);
    assert!(is_normalized(&union_iter_1));

    // Check against the vector-based union.
    let simple_union = x.into_union(y);
    assert_eq!(union_iter_1, simple_union);
}

fuzz_target!(|x_y: (Vec<(T, T)>, Vec<(T, T)>)| {
    let (x, y) = x_y;
    check(x.clone(), y.clone());
    check_single(x.clone());

    let x = x
        .into_iter()
        .map(|(a, b)| (a.min(b), a.max(b)))
        .collect::<Vec<_>>();
    let y = y
        .into_iter()
        .map(|(a, b)| (a.min(b), a.max(b)))
        .collect::<Vec<_>>();
    check(y.clone(), x);
    check_single(y);
});
