#![no_main]

use closed_interval_set::is_normalized;
use closed_interval_set::Endpoint;
use closed_interval_set::RangeVec;

use libfuzzer_sys::fuzz_target;

type T = f32;

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
        let universe = RangeVec::from_vec(vec![(T::NEG_INFINITY, T::INFINITY)]);
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

        assert_eq!(universe.inner(), &[(T::NEG_INFINITY, T::INFINITY)]);
    }
    // x | x = x
    {
        let double = x.iter().union(x.iter()).collect_range_vec();

        assert_eq!(&x, &double);
    }

    // x | -x = universe
    {
        let universe = x.iter().union(x.iter().complement()).collect_range_vec();

        assert_eq!(universe.inner(), &[(T::NEG_INFINITY, T::INFINITY)]);
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
        .map(|(a, b)| (a.bot_end(b), a.top_end(b)))
        .collect::<Vec<_>>();
    let y = y
        .into_iter()
        .map(|(a, b)| (a.bot_end(b), a.top_end(b)))
        .collect::<Vec<_>>();
    check(y.clone(), x);
    check_single(y);
});
