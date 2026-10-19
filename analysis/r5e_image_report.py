"""Round 5, question 85: the image and the in-degrees against the model.

Reads data/r5e_image_summary.txt and the per-class tables
data/r5e_image_b<b>_m1.txt of `dyn_cycles --image`, and
data/r5e_image_sim_*.txt of r5e_image_sim.py. Per base: the image share
against three versions of the class-lumped random mapping (uniform inside a
class as in question 85, weighted by the number of strings, and weighted
over the distinct values of S only), the shares by length, and the law of
the in-degree of the distinct values (mean, variance / mean, tail) against
the Poisson mixture of the model. Output: data/r5e_image_report.txt.
"""
import glob
import os
import re
from collections import defaultdict

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(HERE, 'data')


def main():
    out = ["# r5e_image_report.py: image of c -> multiset of S(c), multisets of 1 to b digits"]
    out.append("# b | multisets | distinct sums | image | share | uniform | weighted | distinct sums "
               "| in-degree of sums: var/mean obs, model | share with in-degree >= 4: obs, model")
    summ = {}
    for line in open(os.path.join(D, 'r5e_image_summary.txt')):
        m = re.match(r'image b=(\d+) m=(\d)', line)
        if m and m.group(2) == '1':
            kv = dict(re.findall(r'(\w+)=([\d.e+-]+)', line))
            summ[int(m.group(1))] = kv
    for b in sorted(summ):
        kv = summ[b]
        path = os.path.join(D, f'r5e_image_b{b}_m1.txt')
        O0 = np.zeros(17)
        P0 = np.zeros(17)
        for line in open(path):
            if line.startswith('#'):
                continue
            parts = line.split('|')
            O0 += np.array(list(map(float, parts[4].split())))
            P0 += np.array(list(map(float, parts[5].split())))
        k = np.arange(17)

        def vm(h):
            n = h.sum()
            mu = (h * k).sum() / n
            var = (h * k * k).sum() / n - mu * mu
            return var / mu

        tail_o = O0[4:].sum() / O0.sum()
        tail_p = P0[4:].sum() / P0.sum()
        out.append(f"{b} | {int(float(kv['multisets']))} | {kv['distinct_sums']} | {kv['image']} | {float(kv['share']):.3f} | "
                   f"{float(kv['share_u']):.3f} | {float(kv['share_w']):.3f} | {float(kv['share_d']):.3f} | "
                   f"{vm(O0):.2f}, {vm(P0):.2f} | {tail_o:.4f}, {tail_p:.4f}")
    # by length, the largest base available
    bmax = max(summ)
    agg = defaultdict(lambda: np.zeros(4))
    for line in open(os.path.join(D, f'r5e_image_b{bmax}_m1.txt')):
        if line.startswith('#'):
            continue
        parts = line.split('|')
        h = parts[0].split()
        d, n = int(h[1]), float(h[3])
        o = list(map(float, parts[1].split()))
        w = list(map(float, parts[2].split()))
        z = list(map(float, parts[5].split()))
        agg[d] += np.array([n, n - o[0], n - w[0], n - z[0]])
    out.append(f"# base {bmax} by length: digits | multisets | image obs | weighted | distinct sums | obs / distinct")
    for d in sorted(agg):
        a = agg[d]
        out.append(f"{d} | {a[0]:.0f} | {a[1]:.0f} | {a[2]:.0f} | {a[3]:.0f} | {a[1] / a[3]:.3f}")
    for f in sorted(glob.glob(os.path.join(D, 'r5e_image_sim_*.txt'))):
        for line in open(f):
            if not line.startswith('#'):
                p = line.split('|')
                b, nv, true = p[0].split()
                sims = p[1].split()
                out.append(f"simulation b={b}: true image {true}; random below the top t digits, t = 0..3: "
                           + ", ".join(sims) + "; share of the gap closed by t = 3: "
                           f"{(float(sims[0]) - float(sims[3])) / (float(sims[0]) - float(true)):.2f}")
    with open(os.path.join(D, 'r5e_image_report.txt'), 'w') as fh:
        fh.write("\n".join(out) + "\n")
    print("\n".join(out))


if __name__ == '__main__':
    main()
