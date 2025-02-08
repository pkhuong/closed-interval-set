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
                fn cmp_end(self, other: Self) -> std::cmp::Ordering {
                    std::cmp::Ord::cmp(&self, &other)
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
