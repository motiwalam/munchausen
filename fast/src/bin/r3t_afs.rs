//! Munchausen numbers in the rational base p/q of Akiyama, Frougny and
//! Sakarovitch (question 60).
//!
//! Every N >= 1 has a unique expansion N = sum (a_i / q) (p/q)^i with digits
//! 0 <= a_i < p, from q N_i = p N_(i+1) + a_i, N_0 = N. The expansion of N is
//! that of its parent N_1 = (q N - a_0) / p followed by a_0, so the integers
//! form a tree: the children of M are the integers (p M + a) / q. A depth-first
//! walk from the root carries F(N) = F(N_1) + w(a_0) at O(1) cost per node.
//!
//! Pruning. The descendants of N at depth t lie in [N r^t, (N+1) r^t), r = p/q,
//! and their sums are at most F(N) + t W, W = (p-1)^(p-1). A descendant D is a
//! solution only if N r^t <= D = F(D) <= F(N) + t W. The subtree is cut when
//! g(t) = N r^t - F(N) - t W > 0 for every t >= 1; g is convex, so it suffices
//! to check g at t = 1 and around its minimum (with a safety margin).
//!
//! Identity: modulo p - q, q N == digit sum, so a solution has
//! sum (q w(a) - a) == 0 (mod p - q).
//!
//! With J > 0 the search also counts the near-solutions N = F(N) + j (p - q),
//! j = 1..J, per convention (section 11.1).
//!
//! usage: r3t_afs search <p> <q> [J]      both conventions 0^0 = 0 and 1
//!        r3t_afs model <p> <q> <samples>  the model per length, by sampling

use rayon::prelude::*;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

struct Cfg {
    p: u64,
    q: u64,
    w: Vec<u64>,
    wmax: u64,
    lnr: f64,
}

struct Out {
    sols: Mutex<Vec<(u32, u64, Vec<u8>)>>,
    nodes: AtomicU64,
}

impl Cfg {
    /// true if no descendant of N (depth >= 1) can be a solution under either convention
    #[inline]
    fn cut(&self, n: u64, f1: u64) -> bool {
        // g(1) = N p / q - f1 - W > 0
        if n * self.p <= (f1 + self.wmax) * self.q {
            return false;
        }
        // g'(t) = N r^t ln r - W; if g'(1) >= 0 then g increases from t = 1
        let nf = n as f64;
        let r = self.p as f64 / self.q as f64;
        if nf * r * self.lnr >= self.wmax as f64 * (1.0 + 1e-9) {
            return true;
        }
        // minimum near t* with N r^t* ln r = W
        let ts = ((self.wmax as f64) / (nf * self.lnr)).ln() / self.lnr;
        let t0 = ts.floor().max(1.0);
        for t in [t0, t0 + 1.0] {
            let g = nf * (t * self.lnr).exp() - f1 as f64 - t * self.wmax as f64;
            if g <= 1.0 + 1e-9 * (f1 as f64 + t * self.wmax as f64) {
                return false;
            }
        }
        true
    }
}

struct Near {
    k: u64,           // offsets are j * k, j = 1..=jmax
    jmax: u64,
    cnt: [Vec<u64>; 2], // per convention
}

#[inline]
fn visit(cfg: &Cfg, n: u64, f0: u64, z: u32, out: &Out, near: &mut Near) {
    for m in 0..2 {
        let f = f0 + m as u64 * z as u64;
        if f == n {
            out.sols.lock().unwrap().push((m, n, expand(n, cfg.p, cfg.q)));
        } else if n > f && near.jmax > 0 {
            let dd = n - f;
            if dd % near.k == 0 && dd / near.k <= near.jmax {
                near.cnt[m as usize][(dd / near.k - 1) as usize] += 1;
            }
        }
    }
}

fn walk(cfg: &Cfg, n: u64, f0: u64, z: u32, out: &Out, cnt: &mut u64, near: &mut Near) {
    *cnt += 1;
    visit(cfg, n, f0, z, out, near);
    if cfg.cut(n, f0 + z as u64 + near.k * near.jmax) {
        return;
    }
    let base = cfg.p * n;
    let a0 = (cfg.q - base % cfg.q) % cfg.q;
    let mut a = a0;
    while a < cfg.p {
        let c = (base + a) / cfg.q;
        walk(cfg, c, f0 + cfg.w[a as usize], z + (a == 0) as u32, out, cnt, near);
        a += cfg.q;
    }
}

fn expand(n: u64, p: u64, q: u64) -> Vec<u8> {
    let mut out = vec![];
    let mut x = n;
    while x > 0 {
        let t = q as u128 * x as u128;
        let a = (t % p as u128) as u64;
        x = ((t - a as u128) / p as u128) as u64;
        out.push(a as u8);
    }
    out.reverse();
    out
}

fn search(p: u64, q: u64, jmax: u64) {
    let w: Vec<u64> = (0..p).map(|a| if a == 0 { 0 } else { a.pow(a as u32) }).collect();
    let cfg = Cfg { p, q, wmax: w[p as usize - 1], w, lnr: (p as f64 / q as f64).ln() };
    let k = p - q;
    let t0 = Instant::now();
    let out = Out { sols: Mutex::new(vec![]), nodes: AtomicU64::new(0) };
    let newnear = || Near { k, jmax, cnt: [vec![0; jmax as usize], vec![0; jmax as usize]] };
    let total = Mutex::new(newnear());
    // split the tree into subtrees a few levels down
    let mut front: Vec<(u64, u64, u32)> = vec![];
    let mut level = vec![(0u64, 0u64, 0u32)];
    let mut extra = 0u64;
    let mut nr = newnear();
    while !level.is_empty() {
        if level.len() >= 20000 {
            front = level;
            break;
        }
        let mut stack = std::mem::take(&mut level);
        let next = &mut level;
        while let Some((n, f0, z)) = stack.pop() {
        extra += 1;
        if n > 0 {
            visit(&cfg, n, f0, z, &out, &mut nr);
            if cfg.cut(n, f0 + z as u64 + k * jmax) {
                continue;
            }
        }
        let base = cfg.p as u128 * n as u128;
        let a0 = ((cfg.q as u128 - base % cfg.q as u128) % cfg.q as u128) as u64;
        let mut a = a0;
        while a < cfg.p {
            let c = ((base + a as u128) / cfg.q as u128) as u64;
            if c > 0 {
                next.push((c, f0 + cfg.w[a as usize], z + (a == 0) as u32));
            }
            a += cfg.q;
        }
        }
    }
    front.par_iter().for_each(|&(n, f0, z)| {
        let mut cnt = 0;
        let mut near = newnear();
        walk(&cfg, n, f0, z, &out, &mut cnt, &mut near);
        out.nodes.fetch_add(cnt, Ordering::Relaxed);
        let mut t = total.lock().unwrap();
        for m in 0..2 {
            for j in 0..jmax as usize {
                t.cnt[m][j] += near.cnt[m][j];
            }
        }
    });
    let mut t = total.into_inner().unwrap();
    for m in 0..2 {
        for j in 0..jmax as usize {
            t.cnt[m][j] += nr.cnt[m][j];
        }
    }
    let mut sols = out.sols.into_inner().unwrap();
    sols.sort();
    for (m, n, path) in &sols {
        let f: u64 = path.iter().map(|&a| if a == 0 { *m as u64 } else { (a as u64).pow(a as u32) }).sum();
        assert_eq!(f, *n);
        println!("sol p/q {p}/{q} m {m} N {n} len {} digits {}", path.len(), path.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","));
    }
    for m in 0..2 {
        let v: Vec<String> = t.cnt[m].iter().map(|x| x.to_string()).collect();
        println!("near p/q {p}/{q} m {m} step {k} counts {}", v.join(","));
    }
    let c0 = sols.iter().filter(|s| s.0 == 0 && s.2.len() >= 2).count();
    let c1 = sols.iter().filter(|s| s.0 == 1 && s.2.len() >= 2).count();
    println!(
        "done p/q {p}/{q} sols0 {c0} sols1 {c1} nodes {} secs {:.1}",
        out.nodes.load(Ordering::Relaxed) + extra,
        t0.elapsed().as_secs_f64()
    );
}

fn length(n: u64, p: u64, q: u64) -> usize {
    let mut x = n;
    let mut k = 0;
    while x > 0 {
        let t = q as u128 * x as u128;
        x = ((t - t % p as u128) / p as u128) as u64;
        k += 1;
    }
    k
}

fn model(p: u64, q: u64, samples: usize) {
    let w: Vec<u64> = (0..p).map(|a| if a == 0 { 0 } else { a.pow(a as u32) }).collect();
    let wmax = w[p as usize - 1];
    let md = p - q;
    // window boundaries: first[L] = smallest N with length L (lengths are nondecreasing in N)
    let first = |l: usize| -> u64 {
        let (mut lo, mut hi) = (1u64, 1u64);
        while length(hi, p, q) < l {
            hi *= 2;
        }
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if length(mid, p, q) >= l { hi = mid } else { lo = mid + 1 }
        }
        lo
    };
    println!("# model p/q {p}/{q}: refined factor {md} on sum (q w(a) - a) == 0 mod {md}");
    let mut tot = [0f64; 6];
    let mut l = 2usize;
    loop {
        let lo = first(l);
        if lo as u128 > (l as u128 + 1) * wmax as u128 {
            break;
        }
        let hi = first(l + 1);
        let acc = Mutex::new([0u64; 6]);
        let chunks = 32usize;
        (0..chunks).into_par_iter().for_each(|ci| {
            let mut s = 0x9e37_79b9_7f4a_7c15u64 ^ (ci as u64).wrapping_mul(0x1234_5678_9abc_def1) ^ ((l as u64) << 40) ^ (p << 50) ^ (q << 56);
            let mut next = || {
                s = s.wrapping_add(0x9e37_79b9_7f4a_7c15);
                let mut z = s;
                z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
                z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
                z ^ (z >> 31)
            };
            let mut a6 = [0u64; 6];
            for _ in 0..samples / chunks {
                let n = lo + next() % (hi - lo);
                let mut x = n;
                let (mut f0, mut zeros, mut res) = (0u64, 0u64, 0u64);
                while x > 0 {
                    let t = q as u128 * x as u128;
                    let a = (t % p as u128) as u64;
                    x = ((t - a as u128) / p as u128) as u64;
                    f0 += w[a as usize];
                    zeros += (a == 0) as u64;
                    res = (res + (q as u128 * w[a as usize] as u128 % md as u128) as u64 + md - a % md) % md;
                }
                for m in 0..2u64 {
                    let f = f0 + m * zeros;
                    let r = (res + m * zeros * q % md) % md;
                    if f >= lo && f < hi {
                        a6[3 * m as usize] += 1;
                        if r == 0 {
                            a6[3 * m as usize + 1] += 1;
                            if zeros == 0 {
                                a6[3 * m as usize + 2] += 1;
                            }
                        }
                    }
                }
            }
            let mut g = acc.lock().unwrap();
            for i in 0..6 {
                g[i] += a6[i];
            }
        });
        let a = acc.into_inner().unwrap();
        let ns = (samples / chunks * chunks) as f64;
        let v: Vec<f64> = (0..6).map(|i| a[i] as f64 / ns * if i % 3 == 0 { 1.0 } else { md as f64 }).collect();
        if v.iter().any(|&x| x > 0.0) {
            println!(
                "len p/q {p}/{q} L {l} window {lo}..{hi} basic0 {:.4e} refined0 {:.4e} zerofree0 {:.4e} basic1 {:.4e} refined1 {:.4e} zerofree1 {:.4e}",
                v[0], v[1], v[2], v[3], v[4], v[5]
            );
        }
        for i in 0..6 {
            tot[i] += v[i];
        }
        l += 1;
    }
    println!(
        "model p/q {p}/{q} basic0 {:.4} refined0 {:.4} zerofree0 {:.4} basic1 {:.4} refined1 {:.4} zerofree1 {:.4}",
        tot[0], tot[1], tot[2], tot[3], tot[4], tot[5]
    );
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let p: u64 = a[2].parse().unwrap();
    let q: u64 = a[3].parse().unwrap();
    match a[1].as_str() {
        "search" => search(p, q, a.get(4).map(|x| x.parse().unwrap()).unwrap_or(0)),
        "model" => model(p, q, a[4].parse().unwrap()),
        _ => panic!("unknown mode"),
    }
}
