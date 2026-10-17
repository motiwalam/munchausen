// Fixed-width base-b numbers stored as one byte per digit, least significant
// digit in lane 0. With N 32-byte words we hold 32*N digits, which is enough
// for any base up to 32*N - 2 without a bignum library.
//
// Addition works lane-wise and then resolves carries with the classic
// carry-lookahead identity on bitmasks:
//     carry_in = ((generate << 1) + propagate) ^ propagate
// where generate = lanes whose sum >= b, propagate = lanes whose sum == b-1.
// All bitmasks fit in a u64 because N <= 2.

pub const MAX_LANES: usize = 64;

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
mod imp {
    use std::arch::x86_64::*;

    #[derive(Clone, Copy)]
    #[repr(C, align(32))]
    pub struct DV<const N: usize>(pub [__m256i; N]);

    #[derive(Clone, Copy)]
    pub struct Base {
        bm1: __m256i, // b-1 in every lane
        bv: __m256i,  // b in every lane
    }

    impl Base {
        pub fn new(b: u32) -> Base {
            unsafe {
                Base {
                    bm1: _mm256_set1_epi8((b - 1) as i8),
                    bv: _mm256_set1_epi8(b as i8),
                }
            }
        }
    }

    // bits 32w..32w+31 of a mask broadcast to every 64-bit lane of v ->
    // bytes that are 0xFF where the bit is set
    #[inline(always)]
    unsafe fn expand(v: __m256i, w: usize) -> __m256i {
        unsafe {
            let o = 4 * w as i8;
            let shuf = _mm256_setr_epi8(
                o, o, o, o, o, o, o, o, o + 1, o + 1, o + 1, o + 1, o + 1, o + 1, o + 1, o + 1, //
                o + 2, o + 2, o + 2, o + 2, o + 2, o + 2, o + 2, o + 2, o + 3, o + 3, o + 3, o + 3, o + 3, o + 3, o + 3, o + 3,
            );
            let v = _mm256_shuffle_epi8(v, shuf);
            let sel = _mm256_set1_epi64x(0x8040201008040201u64 as i64);
            _mm256_cmpeq_epi8(_mm256_and_si256(v, sel), sel)
        }
    }

    impl<const N: usize> DV<N> {
        #[inline(always)]
        pub fn zero() -> Self {
            unsafe { DV([_mm256_setzero_si256(); N]) }
        }

        pub fn from_bytes(x: &[u8; 64]) -> Self {
            let mut out = Self::zero();
            unsafe {
                for i in 0..N {
                    out.0[i] = _mm256_loadu_si256(x.as_ptr().add(32 * i) as *const __m256i);
                }
            }
            out
        }

        #[inline(always)]
        pub fn to_bytes(&self, out: &mut [u8; 64]) {
            unsafe {
                for i in 0..N {
                    _mm256_storeu_si256(out.as_mut_ptr().add(32 * i) as *mut __m256i, self.0[i]);
                }
            }
        }

        #[inline(always)]
        pub fn add(&self, o: &Self, base: &Base) -> Self {
            unsafe {
                let mut s = [_mm256_setzero_si256(); N];
                let mut g = 0u64;
                let mut p = 0u64;
                for i in 0..N {
                    s[i] = _mm256_add_epi8(self.0[i], o.0[i]);
                    // lane sums reach 2b-1 > 127, so compare unsigned: s >= b iff max(s, b) == s
                    let ge = _mm256_cmpeq_epi8(_mm256_max_epu8(s[i], base.bv), s[i]);
                    g |= (_mm256_movemask_epi8(ge) as u32 as u64) << (32 * i);
                    p |= (_mm256_movemask_epi8(_mm256_cmpeq_epi8(s[i], base.bm1)) as u32 as u64) << (32 * i);
                }
                let cin = ((g << 1).wrapping_add(p)) ^ p;
                let mut out = Self::zero();
                // one move into a vector register serves both words
                let cv = _mm256_set1_epi64x(cin as i64);
                for i in 0..N {
                    // subtracting 0xFF adds one
                    let r = _mm256_sub_epi8(s[i], expand(cv, i));
                    // r <= 2b-1 < 256; if r < b then r - b wraps above r
                    out.0[i] = _mm256_min_epu8(r, _mm256_sub_epi8(r, base.bv));
                }
                out
            }
        }

        // bit i set iff lane i of self equals lane i of o
        #[inline(always)]
        pub fn eq_mask(&self, o: &Self) -> u64 {
            unsafe {
                let mut m = 0u64;
                for i in 0..N {
                    m |= (_mm256_movemask_epi8(_mm256_cmpeq_epi8(self.0[i], o.0[i])) as u32 as u64) << (32 * i);
                }
                m
            }
        }

        // bit i set iff lane i equals x
        #[inline(always)]
        pub fn eq_byte_mask(&self, x: u8) -> u64 {
            unsafe {
                let v = _mm256_set1_epi8(x as i8);
                let mut m = 0u64;
                for i in 0..N {
                    m |= (_mm256_movemask_epi8(_mm256_cmpeq_epi8(self.0[i], v)) as u32 as u64) << (32 * i);
                }
                m
            }
        }

        // bit j set iff lane j equals x[i]; the broadcast reads x[i] from
        // memory and skips a move through a general register
        #[inline(always)]
        pub fn eq_mask_at(&self, x: &[u8; 64], i: usize) -> u64 {
            unsafe {
                let v = _mm256_broadcastb_epi8(_mm_loadu_si16(x.as_ptr().add(i & 63) as *const u8));
                let mut m = 0u64;
                for i in 0..N {
                    m |= (_mm256_movemask_epi8(_mm256_cmpeq_epi8(self.0[i], v)) as u32 as u64) << (32 * i);
                }
                m
            }
        }

        // bit i set iff lane i is at least x
        #[inline(always)]
        pub fn ge_mask(&self, x: u8) -> u64 {
            unsafe {
                let v = _mm256_set1_epi8(x as i8);
                let mut m = 0u64;
                for i in 0..N {
                    let ge = _mm256_cmpeq_epi8(_mm256_max_epu8(self.0[i], v), self.0[i]);
                    m |= (_mm256_movemask_epi8(ge) as u32 as u64) << (32 * i);
                }
                m
            }
        }

        // bit i set iff lane i is nonzero
        #[inline(always)]
        pub fn nonzero_mask(&self) -> u64 {
            unsafe {
                let z = _mm256_setzero_si256();
                let mut m = 0u64;
                for i in 0..N {
                    m |= (_mm256_movemask_epi8(_mm256_cmpeq_epi8(self.0[i], z)) as u32 as u64) << (32 * i);
                }
                if N == 1 { !m & 0xffff_ffff } else { !m }
            }
        }
    }
}

#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
mod imp {
    // portable fallback: same semantics, plain loops
    #[derive(Clone, Copy)]
    #[repr(C, align(32))]
    pub struct DV<const N: usize>(pub [[u8; 32]; N]);

    #[derive(Clone, Copy)]
    pub struct Base {
        b: u8,
    }

    impl Base {
        pub fn new(b: u32) -> Base {
            Base { b: b as u8 }
        }
    }

    impl<const N: usize> DV<N> {
        #[inline(always)]
        pub fn zero() -> Self {
            DV([[0; 32]; N])
        }

        pub fn from_bytes(x: &[u8; 64]) -> Self {
            let mut out = Self::zero();
            for i in 0..32 * N {
                out.0[i / 32][i % 32] = x[i];
            }
            out
        }

        #[inline(always)]
        pub fn to_bytes(&self, out: &mut [u8; 64]) {
            for i in 0..32 * N {
                out[i] = self.0[i / 32][i % 32];
            }
        }

        #[inline(always)]
        pub fn add(&self, o: &Self, base: &Base) -> Self {
            let mut out = Self::zero();
            let mut c = 0u8;
            for i in 0..32 * N {
                let mut s = self.0[i / 32][i % 32].wrapping_add(o.0[i / 32][i % 32]).wrapping_add(c);
                c = (s >= base.b) as u8;
                if c == 1 {
                    s -= base.b;
                }
                out.0[i / 32][i % 32] = s;
            }
            out
        }

        #[inline(always)]
        pub fn eq_mask(&self, o: &Self) -> u64 {
            let mut m = 0u64;
            for i in 0..32 * N {
                m |= ((self.0[i / 32][i % 32] == o.0[i / 32][i % 32]) as u64) << i;
            }
            m
        }

        #[inline(always)]
        pub fn eq_byte_mask(&self, x: u8) -> u64 {
            let mut m = 0u64;
            for i in 0..32 * N {
                m |= ((self.0[i / 32][i % 32] == x) as u64) << i;
            }
            m
        }

        #[inline(always)]
        pub fn eq_mask_at(&self, x: &[u8; 64], i: usize) -> u64 {
            self.eq_byte_mask(x[i & 63])
        }

        #[inline(always)]
        pub fn ge_mask(&self, x: u8) -> u64 {
            let mut m = 0u64;
            for i in 0..32 * N {
                m |= ((self.0[i / 32][i % 32] >= x) as u64) << i;
            }
            m
        }

        #[inline(always)]
        pub fn nonzero_mask(&self) -> u64 {
            let mut m = 0u64;
            for i in 0..32 * N {
                m |= ((self.0[i / 32][i % 32] != 0) as u64) << i;
            }
            m
        }
    }
}

pub use imp::{Base, DV};

impl<const N: usize> DV<N> {
    /// the digit in lane i
    #[inline(always)]
    pub fn lane(&self, i: u32) -> u8 {
        let mut x = [0u8; 64];
        self.to_bytes(&mut x);
        x[i as usize & 63]
    }

    /// how many of the lanes selected by mask hold x
    #[inline(always)]
    pub fn count(&self, x: u8, mask: u64) -> u32 {
        (self.eq_byte_mask(x) & mask).count_ones()
    }
}

/// digits of a BigUint in base b, least significant first, padded to 64 lanes
pub fn big_to_lanes(x: &num_bigint::BigUint, b: u32) -> [u8; 64] {
    let mut out = [0u8; 64];
    for (i, d) in x.to_radix_le(b).into_iter().enumerate() {
        assert!(i < MAX_LANES, "number too large for digit vector");
        out[i] = d;
    }
    out
}
