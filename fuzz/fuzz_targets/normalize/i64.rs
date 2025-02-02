#![no_main]

use closed_interval_set::is_normalized;
use closed_interval_set::normalize_vec;
use closed_interval_set::RangeVec;

use libfuzzer_sys::fuzz_target;

// for SIGN in i u; do for W in 8 16 32 64 128; do cp template.rs $SIGN$W.rs; sed -i -re "s/type T = [ui][0-9]+;/type T = $SIGN$W;/" $SIGN$W.rs; done; done

type T = i64;

fn ranges_to_marks(ranges: &[(T, T)]) -> Option<Vec<u64>> {
    if std::mem::size_of::<T>() > 2 {
        return None;
    }

    // 2 bytes count up to 64K, so we can clamp everything to +/- 100k
    let limit = ((T::MAX as isize).max(100_000) - (T::MIN as isize).min(-100_000)) as usize + 1;
    let num_words = limit.div_ceil(64);
    let mut ret = vec![0u64; num_words];
    for (start, stop) in ranges.iter().copied() {
        if start > stop {
            continue;
        }

        for i in start..=stop {
            let i = ((i as isize) - (T::MIN as isize)) as usize;
            assert!(i < limit);
            let word = i / 64;
            let bit = i % 64;
            ret[word] |= 1u64 << bit;
        }
    }

    Some(ret)
}

fn independent_is_normalized(ranges: &[(T, T)]) -> bool {
    // All valid ranges
    for (start, stop) in ranges.iter().copied() {
        if start > stop {
            return false;
        }
    }

    // Sorted, with some gap between the ranges.
    for ((_, first), (second, _)) in ranges.iter().copied().zip(ranges.iter().skip(1).copied()) {
        if first >= second {
            return false;
        }

        // first < second, so we can increment first by 1.
        if first + 1 >= second {
            return false;
        }
    }

    true
}

fn check(ranges: Vec<(T, T)>) {
    let initial_marks = ranges_to_marks(&ranges);

    let ranges = if is_normalized(&ranges) {
        // If the input is normalised already, normalizing should be a
        // no-op.
        assert!(independent_is_normalized(&ranges));
        let normalized = RangeVec::from_vec(ranges.clone());
        assert_eq!(normalized.inner(), &ranges);
        normalized
    } else {
        assert!(!independent_is_normalized(&ranges));
        let normalized = RangeVec::from_vec(ranges.clone());
        assert!(normalized.inner() != &ranges);
        normalized
    };

    // The result must represent the same values.
    assert_eq!(&initial_marks, &ranges_to_marks(ranges.inner()));

    // The result must be normalized.
    assert!(is_normalized(ranges.inner()));

    // Double check by hand.
    assert!(independent_is_normalized(&ranges));

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
        .map(|(x, y)| (x.min(y), x.max(y)))
        .collect::<Vec<_>>();

    check(ranges.clone());

    // Run on normalized input;
    check(normalize_vec(ranges).into_inner());
});
