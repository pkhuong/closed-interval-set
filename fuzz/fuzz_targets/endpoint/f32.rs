#![no_main]

use closed_interval_set::Endpoint;
use libfuzzer_sys::fuzz_target;

type T = f32;

fn single_endpoint(x: T) {
    assert_eq!(<T as Endpoint>::max_value(), T::INFINITY);
    assert_eq!(<T as Endpoint>::min_value(), T::NEG_INFINITY);

    if x != T::INFINITY && !x.is_nan() {
        let y = x.next_after().unwrap();
        assert_eq!(y.total_cmp(&x), std::cmp::Ordering::Greater);
    } else if !x.is_nan() {
        assert_eq!(x.next_after(), None);
    }

    if x != T::NEG_INFINITY && !x.is_nan() {
        let y = x.prev_before().unwrap();
        assert_eq!(y.total_cmp(&x), std::cmp::Ordering::Less);
    } else if !x.is_nan() {
        assert_eq!(x.prev_before(), None);
    }
}

fn two_endpoints(x: T, y: T) {
    assert_eq!(x.total_cmp(&y), x.cmp_end(y));
    assert_eq!(y.total_cmp(&x), y.cmp_end(x));

    let (x, y) = if x.total_cmp(&y) <= std::cmp::Ordering::Equal {
        (x, y)
    } else {
        (y, x)
    };

    assert_eq!(x.decrease_toward(y), None);
    assert_eq!(y.increase_toward(x), None);

    if x.to_bits() == y.to_bits() {
        assert_eq!(x.increase_toward(y), None);
        assert_eq!(x.decrease_toward(y), None);
        assert_eq!(y.increase_toward(x), None);
        assert_eq!(y.decrease_toward(x), None);
    } else {
        let z = x.increase_toward(y).unwrap();
        assert_eq!(z.total_cmp(&x), std::cmp::Ordering::Greater);

        let z = y.decrease_toward(x).unwrap();
        assert_eq!(z.total_cmp(&y), std::cmp::Ordering::Less);
    }
}

fuzz_target!(|values: Vec<(T, T)>| {
    for (x, y) in values {
        single_endpoint(x);
        single_endpoint(y);
        two_endpoints(x, y);
    }
});
