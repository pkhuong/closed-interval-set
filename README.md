Closed interval set: disjoint unions of closed intervals
========================================================

[Real documentation on docs.rs](https://docs.rs/closed-interval-set).

There's a plethora of crates that manipulate sets of values
represented as sets of intervals.  This crate targets what appears to
be a gap in the current (February 2025) offering:

1. Support for all standard machine integer (include 128-bit integers)
   as endpoints
2. Ability to represent the universe `[T::MIN, T::MAX`]
3. No unchecked overflow

The `closed-interval-set` crate offers all that, for arbitrary types
that implement its `Endpoint` trait, and comes with an implementation
of that trait for the 12 standard integer types, as well as for 32 and
64 -bit floats.

The crate is designed for usage patterns where sets are constructed
ahead of time (perhaps by combining different sets together), then
frozen (as `SmallVec<[(T, T); 2]>`, internally) for read-only access.
However, its iterator implementations of set complementation, union,
and intersection are closed over the `NormalizedRangeIter` trait, so
it's feasible to build up complex, even type-erased, expression before
materializing the result to a `RangeVec`.

Related crates
--------------

[normalize\_interval](https://crates.io/crates/normalize_interval) : same idea of normalizing
integer ranges to closed intervals.

Many crates can handle the more complex case where we wish to track
overlapping ranges individually (e.g., [iset](https://crates.io/crates/iset),
or [nested_intervals](https://crates.io/crates/nested_intervals)).

The [range-set-blaze](https://crates.io/crates/range-set-blaze) is
similar to this crate, and [intervallum](https://crates.io/crates/intervallum)
even closer, but neither handles the full range of u128 or i128.
