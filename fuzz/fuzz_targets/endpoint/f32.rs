#![no_main]

use closed_interval_set::Endpoint;
use libfuzzer_sys::fuzz_target;

type T = f32;

fn single_endpoint(x: T) {
    assert_eq!(<T as Endpoint>::max_value(), T::INFINITY);
    assert_eq!(<T as Endpoint>::min_value(), T::NEG_INFINITY);

    if x != T::INFINITY && !x.is_nan() {
        let y = x.next_after().unwrap();
        if x != 0.0 {
            assert_eq!(y.partial_cmp(&x), Some(std::cmp::Ordering::Greater));
        }
    } else if !x.is_nan() {
        assert_eq!(x.next_after(), None);
    }

    if x != T::NEG_INFINITY && !x.is_nan() {
        let y = x.prev_before().unwrap();
        if x != 0.0 {
            assert_eq!(y.partial_cmp(&x), Some(std::cmp::Ordering::Less));
        }
    } else if !x.is_nan() {
        assert_eq!(x.prev_before(), None);
    }
}

fn two_endpoints(x: T, y: T) {
    if x == 0.0 || y == 0.0 {
        // signed zeros are tested elsewhere.
        return;
    }
    let (x, y) = match x.partial_cmp(&y) {
        Some(ord) if ord <= std::cmp::Ordering::Equal => (x, y),
        Some(_) => (y, x),
        None => return,
    };

    assert_eq!(x.decrease_toward(y), None);
    assert_eq!(y.increase_toward(x), None);

    if x == y {
        assert_eq!(x.increase_toward(y), None);
        assert_eq!(x.decrease_toward(y), None);
        assert_eq!(y.increase_toward(x), None);
        assert_eq!(y.decrease_toward(x), None);
    } else {
        let z = x.increase_toward(y).unwrap();
        assert_eq!(z.partial_cmp(&x), Some(std::cmp::Ordering::Greater));

        let z = y.decrease_toward(x).unwrap();
        assert_eq!(z.partial_cmp(&y), Some(std::cmp::Ordering::Less));
    }
}

fuzz_target!(|values: Vec<(T, T)>| {
    for (x, y) in values {
        single_endpoint(x);
        single_endpoint(y);
        two_endpoints(x, y);
    }
});
