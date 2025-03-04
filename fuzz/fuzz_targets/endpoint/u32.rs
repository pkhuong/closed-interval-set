#![no_main]

use closed_interval_set::Endpoint;
use closed_interval_set::RangeVec;
use libfuzzer_sys::fuzz_target;

type T = u32;

fn single_endpoint(x: T) {
    assert_eq!(<T as Endpoint>::max_value(), T::MAX);
    assert_eq!(<T as Endpoint>::min_value(), T::MIN);

    if x != T::MAX {
        assert_eq!(x.next_after(), Some(x + 1));
    } else {
        assert_eq!(x.next_after(), None);
    }

    if x != T::MIN {
        assert_eq!(x.prev_before(), Some(x - 1));
    } else {
        assert_eq!(x.prev_before(), None);
    }
}

fn two_endpoints(x: T, y: T) {
    let (x, y) = (x.min(y), x.max(y));

    assert_eq!(x.decrease_toward(y), None);
    assert_eq!(y.increase_toward(x), None);

    if x == y {
        assert_eq!(x.increase_toward(y), None);
        assert_eq!(x.decrease_toward(y), None);
        assert_eq!(y.increase_toward(x), None);
        assert_eq!(y.decrease_toward(x), None);
    } else {
        assert_eq!(x.increase_toward(y), Some(x + 1));
        assert_eq!(y.decrease_toward(x), Some(y - 1));
    }
}

fuzz_target!(|values: (Vec<(T, T)>, Vec<(T, T)>)| {
    let (first, second) = values;

    {
        let first = RangeVec::from_vec(first.clone());
        let second = RangeVec::from_vec(second.clone());

        let equal = first == second;
        let eqv = first.eqv(&second);

        assert_eq!(equal, eqv);
        assert!(first.eqv(&first));
        assert!(second.eqv(&second));
    }

    for (x, y) in first.into_iter().chain(second.into_iter()) {
        single_endpoint(x);
        single_endpoint(y);
        two_endpoints(x, y);
    }
});
