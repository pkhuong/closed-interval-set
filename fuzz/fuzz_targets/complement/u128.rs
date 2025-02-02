#![no_main]

use closed_interval_set::complement_vec;
use closed_interval_set::is_normalized;
use closed_interval_set::union_vec;
use closed_interval_set::RangeVec;

use libfuzzer_sys::fuzz_target;

// for SIGN in i u; do for W in 8 16 32 64 128; do cp template.rs $SIGN$W.rs; sed -i -re "s/type T = [ui][0-9]+;/type T = $SIGN$W;/" $SIGN$W.rs; done; done

type T = u128;

// Check that the union of a range and its complement yields the
// universe.
fn check(ranges: Vec<(T, T)>) {
    use closed_interval_set::NormalizedRangeIter;

    let ranges = RangeVec::from_vec(ranges);
    assert!(is_normalized(ranges.inner()));

    let complement_1 = ranges.iter().complement().collect_range_vec();
    let complement_2 = complement_vec(ranges.clone());

    assert!(is_normalized(complement_1.inner()));
    assert!(is_normalized(complement_2.inner()));
    assert_eq!(&complement_1, &complement_2);

    // intersection(ranges, complement) == emptyset
    let intersection_1 = ranges
        .iter()
        .intersect_vec(&complement_1)
        .collect_range_vec();
    let intersection_2 = complement_2.intersect(&ranges);
    assert!(is_normalized(intersection_1.inner()));
    assert!(is_normalized(intersection_2.inner()));
    assert!(intersection_1.is_empty());
    assert!(intersection_2.is_empty());

    let universe_1 = union_vec(complement_1, &ranges);
    let universe_2 = union_vec(complement_2, &ranges);

    assert_eq!(universe_1.inner(), &[(T::MIN, T::MAX)]);
    assert_eq!(universe_2.inner(), &[(T::MIN, T::MAX)]);
    assert_eq!(&universe_1, &universe_2);

    let empty_1 = complement_vec(universe_1);
    let empty_2 = complement_vec(universe_2);
    assert_eq!(empty_1.inner(), &[]);
    assert_eq!(empty_2.inner(), &[]);
    assert_eq!(&empty_1, &empty_2);
}

fuzz_target!(|ranges: Vec<(T, T)>| {
    check(ranges.clone());

    // Same with all non-empty ranges
    check(
        ranges
            .into_iter()
            .map(|(a, b)| (a.min(b), a.max(b)))
            .collect::<Vec<_>>(),
    );
});
