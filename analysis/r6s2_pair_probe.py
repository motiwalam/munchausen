"""Round 6, search 2: the instrumented build for r6s2_pair.py.

Usage: python r6s2_pair_probe.py <fast directory>

Patches fast/src/search.rs and fast/src/main.rs of a checkout at the commit
that added the last-digit tests (do not commit the result). The build then
reads PAIR_TEST (0 to 5, see r6s2_pair.py) and tests every node with two
free slots, after its forced digits, by enumerating the pairs. With
PAIR_TEST = 1 to 5 it drops the nodes that fail; with 11 to 15 it only
counts them. Run it with --low-digits 0 --low-pairs 0 for the tables of
the draft, as `PAIR_TEST=v fast search b -j 4 --low-digits 0 --low-pairs 0`.
"""
# Measurement build: an exact, slow test on nodes with two free slots.
# PAIR_TEST=v selects what a pair (y1, y2), y1 <= y2 < k, must satisfy:
#   1: the residue mod b - 1 and S in the clipped interval of the node
#   2: 1, and the digit of S at the first unknown position (lane pp - 1)
#      is a digit the unknown positions can hold
#   3: 1, and the last digit of S is such a digit
#   4: 1, 2 and 3
#   5: S is a solution (its digits are exactly the multiset)
# Counters: rf=2 nodes tested, and failed, printed at exit by main.
import sys
FAST = sys.argv[1]
p = FAST + '/src/search.rs'
s=open(p).read()
def rep(old,new,cnt=1):
    global s
    assert s.count(old)==cnt,(old,s.count(old))
    s=s.replace(old,new)
rep('''    div2: Vec<[u8; 2]>,
}''','''    div2: Vec<[u8; 2]>,
    pair: u8,
}
pub static PAIR_TESTED: AtomicU64 = AtomicU64::new(0);
pub static PAIR_FAILED: AtomicU64 = AtomicU64::new(0);
pub static PAIR_EXACT_FAILED: AtomicU64 = AtomicU64::new(0);''')
rep('''            div2: (0..b2).map(|s| [(s % b) as u8, (s / b) as u8]).collect(),
        }''','''            div2: (0..b2).map(|s| [(s % b) as u8, (s / b) as u8]).collect(),
            pair: std::env::var("PAIR_TEST").ok().and_then(|v| v.parse().ok()).unwrap_or(0),
        }''')
rep('''    // the decided digits above k that the known leading digits do not hold''','''    // measurement: whether some pair passes test v (see the patch header)
    fn pair_ok(&self, k: usize, c: &Node<N>, cnt: &Hist, v: u8) -> bool {
        let d = self.d as usize;
        let known = self.known(c.pp);
        let lo = self.clip_lo(&c.t);
        let z = lo.count(0, known) as usize;
        let avail = self.node_avail(c, k - 1, cnt);
        let mut ld = [0u8; 64];
        lo.to_bytes(&mut ld);
        for m in 0..2 {
            if self.rmodes & (1 << m) == 0 {
                continue;
            }
            for y2 in 0..k {
                for y1 in 0..=y2 {
                    let r = (c.res[m] as u32 + self.rres[m * (self.kmax + 1) + y1] as u32 + self.rres[m * (self.kmax + 1) + y2] as u32) % self.q as u32;
                    if r != 0 {
                        continue;
                    }
                    let c0 = z + (y1 == 0) as usize + (y2 == 0) as usize;
                    let sv = c.t.add(&self.zsum[m * (d + 1) + c0], &self.base).add(&self.w[y1], &self.base).add(&self.w[y2], &self.base);
                    let nz = sv.nonzero_mask();
                    if nz & !self.dmask != 0 || nz & (1 << (d - 1)) == 0 {
                        continue;
                    }
                    let mut sd = [0u8; 64];
                    sv.to_bytes(&mut sd);
                    if (0..d).any(|i| known >> i & 1 != 0 && sd[i] != ld[i]) {
                        continue;
                    }
                    let av = avail | 1 << y1 | 1 << y2;
                    let top = sd[c.pp as usize - 1];
                    let last = sd[0];
                    let ok = match v {
                        1 => true,
                        2 => av >> top & 1 != 0,
                        3 => av >> last & 1 != 0,
                        4 => av >> top & 1 != 0 && av >> last & 1 != 0,
                        _ => {
                            let mut h = [0u8; 128];
                            for &x in &sd[..d] {
                                h[x as usize] += 1;
                            }
                            let mut want = *cnt;
                            for x in 0..k {
                                want[x] = lo.count(x as u8, known) as u8;
                            }
                            want[y1] += 1;
                            want[y2] += 1;
                            h == want
                        }
                    };
                    if ok {
                        return true;
                    }
                }
            }
        }
        false
    }

    // the decided digits above k that the known leading digits do not hold''')
rep('''                && (c.rf != 1 || (p.res_ok(k, c.res)''','''                && (c.rf != 2 || p.pair == 0 || {
                    PAIR_TESTED.fetch_add(1, Ordering::Relaxed);
                    if !p.pair_ok(k, &c, cnt, 5) {
                        PAIR_EXACT_FAILED.fetch_add(1, Ordering::Relaxed);
                    }
                    let ok = p.pair_ok(k, &c, cnt, p.pair % 10);
                    if !ok {
                        PAIR_FAILED.fetch_add(1, Ordering::Relaxed);
                    }
                    ok || p.pair >= 10
                })
                && (c.rf != 1 || (p.res_ok(k, c.res)''')
open(p,'w').write(s)
p2 = FAST + '/src/main.rs'
s=open(p2).read()
old='''    eprintln!("  base {b}: {} nodes, {} interval evaluations", sr.nodes(), sr.evals());'''
assert s.count(old)==1
s=s.replace(old,old+'''
    eprintln!("  pair: tested {} failed {} exact-failed {}", search::PAIR_TESTED.swap(0, std::sync::atomic::Ordering::Relaxed), search::PAIR_FAILED.swap(0, std::sync::atomic::Ordering::Relaxed), search::PAIR_EXACT_FAILED.swap(0, std::sync::atomic::Ordering::Relaxed));''')
open(p2,'w').write(s)
