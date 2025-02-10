#![no_main]

use closed_interval_set::is_normalized;
use closed_interval_set::normalize_vec;
use closed_interval_set::Endpoint;
use closed_interval_set::RangeVec;

use libfuzzer_sys::fuzz_target;

type T = f32;

fn check(ranges: Vec<(T, T)>) {
    let ranges = if is_normalized(&ranges) {
        // If the input is normalised already, normalizing should be a
        // no-op.
        let normalized = RangeVec::from_vec(ranges.clone());
        assert_eq!(normalized.inner(), &ranges);
        normalized
    } else {
        let normalized = RangeVec::from_vec(ranges.clone());
        assert!(normalized.inner() != ranges);
        normalized
    };

    // The result must be normalized.
    assert!(is_normalized(ranges.inner()));

    // Normalizing again should be a no-op.
    assert_eq!(&ranges, &RangeVec::from_vec(ranges.to_vec()));
}

fuzz_target!(|ranges: Vec<(T, T)>| {
    // Exercise full logic
    check(ranges.clone());

    // Half the ranges will be invalid, so also test with valid
    // ranges only.
    let ranges = ranges
        .into_iter()
        .map(|(x, y)| (x.bot_end(y), x.top_end(y)))
        .collect::<Vec<_>>();

    check(ranges.clone());

    // Run on normalized input;
    check(normalize_vec(ranges).into_vec());
});
