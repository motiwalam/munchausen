// Simple reference implementations used to validate the fast search:
// a brute force over all n, and a straightforward u128 version of the
// prefix-pruned DFS (bases <= 27).


pub fn weights(b: u32, mode: u32) -> Vec<u128> {
    (0..b).map(|k| if k == 0 { mode as u128 } else { (k as u128).pow(k) }).collect()
}

pub fn digits_le(mut x: u128, b: u32) -> Vec<u32> {
    let mut v = vec![];
    while x > 0 {
        v.push((x % b as u128) as u32);
        x /= b as u128;
    }
    v
}

fn fsum(n: u128, b: u32, w: &[u128]) -> u128 {
    if n == 0 {
        return w[0];
    }
    digits_le(n, b).iter().map(|&x| w[x as usize]).sum()
}

// ---------- brute force ----------
pub fn brute(b: u32, mode: u32) -> Vec<u128> {
    let w = weights(b, mode);
    let lim = (b as u128) * w[b as usize - 1].max(1);
    let mut out = vec![];
    for n in 0..=lim {
        if fsum(n, b, &w) == n && !(n == 0 && mode == 1) {
            out.push(n);
        }
    }
    out
}

// ---------- prefix-pruned DFS ----------
struct Dfs<'a> {
    b: u32,
    d: u32,
    w: &'a [u128],
    minw: Vec<u128>,
    maxw: Vec<u128>,
    lo_bound: u128,
    hi_bound: u128,
    cnt: [u32; 64],
    nodes: u64,
    found: Vec<u128>,
}

impl<'a> Dfs<'a> {
    fn digits_be(&self, mut x: u128, out: &mut [u32; 64]) {
        for i in (0..self.d as usize).rev() {
            out[i] = (x % self.b as u128) as u32;
            x /= self.b as u128;
        }
    }

    // digits >= k decided (cnt), r slots remain for digits < k
    fn prefix_ok(&self, lo: u128, hi: u128, k: usize, r: u32) -> bool {
        let lo = lo.max(self.lo_bound);
        let hi = hi.min(self.hi_bound);
        let mut dl = [0u32; 64];
        let mut dh = [0u32; 64];
        self.digits_be(lo, &mut dl);
        self.digits_be(hi, &mut dh);
        let mut occ = [0u32; 64];
        let mut low = 0;
        for i in 0..self.d as usize {
            if dl[i] != dh[i] {
                break;
            }
            let x = dl[i] as usize;
            if x >= k {
                occ[x] += 1;
                if occ[x] > self.cnt[x] {
                    return false;
                }
            } else {
                low += 1;
                if low > r {
                    return false;
                }
            }
        }
        true
    }

    fn rec(&mut self, k: usize, r: u32, s: u128) {
        self.nodes += 1;
        if k == 0 {
            let total = s + r as u128 * self.w[0];
            // prefix_ok at k=1 with lo == hi already verified the full digit multiset
            self.found.push(total);
            return;
        }
        let wk = self.w[k];
        if s > self.hi_bound {
            return;
        }
        let maxc = if wk == 0 { r } else { (r as u128).min((self.hi_bound - s) / wk) as u32 };
        for c in 0..=maxc {
            let s2 = s + c as u128 * wk;
            let r2 = r - c;
            let lo = s2.saturating_add(r2 as u128 * self.minw[k]);
            let hi = s2.saturating_add(r2 as u128 * self.maxw[k]);
            if hi < self.lo_bound {
                continue;
            }
            if lo > self.hi_bound {
                break;
            }
            self.cnt[k] = c;
            if k == 1 {
                self.cnt[0] = r2;
            }
            if !self.prefix_ok(lo, hi, if k == 1 { 0 } else { k }, if k == 1 { 0 } else { r2 }) {
                continue;
            }
            self.rec(k - 1, r2, s2);
        }
        self.cnt[k] = 0;
    }
}

pub fn dfs_search(b: u32, mode: u32) -> (Vec<u128>, u64) {
    let w = weights(b, mode);
    let mut all = vec![];
    let mut nodes = 0;
    for d in 1..=b {
        let mut minw = vec![0u128; b as usize];
        let mut maxw = vec![0u128; b as usize];
        for k in 1..b as usize {
            minw[k] = *w[..k].iter().min().unwrap();
            maxw[k] = *w[..k].iter().max().unwrap();
        }
        let bb = b as u128;
        let mut st = Dfs {
            b,
            d,
            w: &w,
            minw,
            maxw,
            lo_bound: if d == 1 { 0 } else { bb.pow(d - 1) },
            hi_bound: bb.checked_pow(d).map(|x| x - 1).unwrap_or(u128::MAX),
            cnt: [0; 64],
            nodes: 0,
            found: vec![],
        };
        st.rec(b as usize - 1, d, 0);
        nodes += st.nodes;
        all.extend(st.found);
    }
    all.retain(|&n| !(n == 0 && mode == 1));
    all.sort();
    all.dedup();
    (all, nodes)
}

