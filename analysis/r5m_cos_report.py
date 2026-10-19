"""Summaries of the output of r5m_cosmin.py (question 80).

usage: python3 r5m_cos_report.py FILE
"""
import collections
import sys


def load(path):
    rows = []
    for line in open(path):
        if line.startswith('#'):
            continue
        a, b, c, d, e, f, g = line.split()
        rows.append((int(a), int(b), int(c), float(d), int(e), float(f), int(g)))
    return rows


def main():
    rows = load(sys.argv[1])
    print("pairs (b, q):", len(rows), " bases:", len({r[0] for r in rows}))
    for lo in (3, 10, 20, 100):
        rs = [r for r in rows if r[0] >= lo]
        m = min(rs, key=lambda r: r[3])
        mm = min(rs, key=lambda r: r[5])
        print(f"b >= {lo}: min c_pois {m[3]:.4f} at (b, q) = {m[:2]} h {m[4]};  min c_mult {mm[5]:.4f} at {mm[:2]}")
    groups = [("q = 3^k", lambda r: r[2] == 3), ("q = 5^k", lambda r: r[2] == 5),
              ("q = 7^k", lambda r: r[2] == 7), ("p >= 11", lambda r: r[2] >= 11),
              ("q = p prime >= 101", lambda r: r[1] == r[2] and r[2] >= 101),
              ("q = p^k, k >= 2", lambda r: r[1] != r[2])]
    print("\ngroup | pairs | min c_pois | at (b, q, h) | min c_mult")
    for name, cond in groups:
        rs = [r for r in rows if cond(r) and r[0] >= 10]
        m = min(rs, key=lambda r: r[3])
        mm = min(rs, key=lambda r: r[5])
        print(f"{name} | {len(rs)} | {m[3]:.4f} | {m[0]}, {m[1]}, {m[4]} | {mm[5]:.4f}")
    print("\nworst primes p >= 101:")
    for r in sorted([r for r in rows if r[1] == r[2] and r[2] >= 101], key=lambda r: r[3])[:8]:
        print("  b %d p %d c_pois %.4f h %d c_mult %.4f %s" % (r[0], r[1], r[3], r[4], r[5], "(b-1 prime)" if r[0] - 1 == r[1] else ""))
    print("\nprimes p >= 101 by size of p: count, min, mean of c_pois")
    bins = collections.defaultdict(list)
    for r in rows:
        if r[1] == r[2] and r[2] >= 101:
            bins[len(str(r[2]))].append(r)
    for k in sorted(bins):
        v = [r[3] for r in bins[k]]
        lp = [r[3] for r in bins[k] if r[0] - 1 == r[1]]
        print(f"  {k}-digit p: {len(v)}, min {min(v):.4f}, mean {sum(v)/len(v):.4f};  b-1 = p: {len(lp)}, min {min(lp):.4f}, mean {sum(lp)/len(lp):.4f}")
    print("\nb - 1 = p prime: max over h of |sum_{x<b} e(h f(x)/p)| / sqrt(p ln p)")
    for lo in (1000, 10000):
        rt = [r[0] * (1 - r[5]) / (r[1] * __import__('math').log(r[1])) ** 0.5
              for r in rows if r[0] - 1 == r[1] == r[2] and r[1] >= lo]
        print(f"  p >= {lo}: {len(rt)} primes, min {min(rt):.3f}, mean {sum(rt)/len(rt):.3f}, max {max(rt):.3f}")
    print("\nratio p/b and c_pois, primes p >= 1000:")
    rb = collections.defaultdict(list)
    for r in rows:
        if r[1] == r[2] and r[2] >= 1000:
            rb[min(int(10 * r[2] / (r[0] - 1)), 9)].append(r[3])
    for k in sorted(rb):
        print(f"  p/(b-1) in [{k/10:.1f}, {(k+1)/10:.1f}): {len(rb[k])}, min {min(rb[k]):.4f}, mean {sum(rb[k])/len(rb[k]):.4f}")


if __name__ == '__main__':
    main()
