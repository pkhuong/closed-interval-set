//! Define the `Endpoint` trait for primitive integer types.

macro_rules! def_endpoint {
    ($($T:ty)*) => {
        $(
            impl crate::Endpoint for $T {
                #[inline(always)]
                fn min_value() -> $T {
                    <$T>::MIN
                }

                #[inline(always)]
                fn max_value() -> $T {
                    <$T>::MAX
                }

                #[inline(always)]
                fn is_valid(self) -> bool {
                    true
                }

                #[inline(always)]
                fn cmp_end(self, other: Self) -> core::cmp::Ordering {
                    core::cmp::Ord::cmp(&self, &other)
                }

                #[inline(always)]
                fn decrease_toward(self, other: $T) -> Option<$T> {
                    if other < self {
                        self.checked_sub(1)
                    } else {
                        None
                    }
                }

                #[inline(always)]
                fn increase_toward(self, other: $T) -> Option<$T> {
                    if other > self {
                        self.checked_add(1)
                    } else {
                        None
                    }
                }
            }
        )*
    };
}

def_endpoint!(i8 i16 i32 i64 i128 isize
              u8 u16 u32 u64 u128 usize);

fn f32_to_i32(x: f32) -> i32 {
    // This is sign-magnitude.  Convert to i32 by flipping all but
    // the top bit when that bit is set.
    let bits = x.to_bits();
    let top = 1u32 << 31;
    let mask = bits & top;

    (bits ^ (mask - (mask >> 31))) as i32
}

fn i32_to_f32(bits: i32) -> f32 {
    // Flip all but the top bit when that bit is set
    let bits = bits as u32;
    let top = 1u32 << 31;
    let mask = bits & top;

    f32::from_bits(bits ^ (mask - (mask >> 31)))
}

fn f64_to_i64(x: f64) -> i64 {
    // This is sign-magnitude.  Convert to i32 by flipping all but
    // the top bit when that bit is set.
    let bits = x.to_bits();
    let top = 1u64 << 63;
    let mask = bits & top;

    (bits ^ (mask - (mask >> 63))) as i64
}

fn i64_to_f64(bits: i64) -> f64 {
    // Flip all but the top bit when that bit is set
    let bits = bits as u64;
    let top = 1u64 << 63;
    let mask = bits & top;

    f64::from_bits(bits ^ (mask - (mask >> 63)))
}

macro_rules! def_float_endpoint {
    ($($T:ty, $to_int:ident, $from_int:ident)*) => {
        $(
            impl crate::Endpoint for $T {
                #[inline(always)]
                fn min_value() -> $T {
                    <$T>::NEG_INFINITY
                }

                #[inline(always)]
                fn max_value() -> $T {
                    <$T>::INFINITY
                }

                #[inline(always)]
                fn is_valid(self) -> bool {
                    !self.is_nan()
                }

                #[inline(always)]
                fn cmp_end(self, other: Self) -> core::cmp::Ordering {
                    $to_int(self).cmp(&$to_int(other))
                }

                #[inline(always)]
                fn decrease_toward(self, other: $T) -> Option<$T> {
                    let this = $to_int(self);
                    let other = $to_int(other);
                    if other < this {
                        this.checked_sub(1).map($from_int)
                    } else {
                        None
                    }
                }

                #[inline(always)]
                fn increase_toward(self, other: $T) -> Option<$T> {
                    let this = $to_int(self);
                    let other = $to_int(other);
                    if other > this {
                        this.checked_add(1).map($from_int)
                    } else {
                        None
                    }
                }
            }
        )*
    };
}

def_float_endpoint!(f32, f32_to_i32, i32_to_f32
                    f64, f64_to_i64, i64_to_f64);

#[cfg(test)]
proptest::proptest! {
    #[test]
    fn test_f32_i32(x: f32, y: f32) {
        use crate::Endpoint;

        assert_eq!(x.to_bits(), i32_to_f32(f32_to_i32(x)).to_bits());
        assert_eq!(y.to_bits(), i32_to_f32(f32_to_i32(y)).to_bits());

        if x.partial_cmp(&0.0) == Some(core::cmp::Ordering::Equal) && y.partial_cmp(&0.0) == Some(core::cmp::Ordering::Equal)  {
            assert_eq!(x.signum().partial_cmp(&y.signum()).unwrap(), x.cmp_end(y));
        } else if let Some(ord) = x.partial_cmp(&y) {
            assert_eq!(ord, x.cmp_end(y));
        }
    }

    #[test]
    fn test_f64_i64(x: f64, y: f64) {
        use crate::Endpoint;

        assert_eq!(x.to_bits(), i64_to_f64(f64_to_i64(x)).to_bits());
        assert_eq!(y.to_bits(), i64_to_f64(f64_to_i64(y)).to_bits());

        if x.partial_cmp(&0.0) == Some(core::cmp::Ordering::Equal) && y.partial_cmp(&0.0) == Some(core::cmp::Ordering::Equal)  {
            assert_eq!(x.signum().partial_cmp(&y.signum()).unwrap(), x.cmp_end(y));
        } else if let Some(ord) = x.partial_cmp(&y) {
            assert_eq!(ord, x.cmp_end(y));
        }
    }
}
