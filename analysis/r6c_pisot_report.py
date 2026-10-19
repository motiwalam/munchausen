"""Question 107: the class factor predicted from the broad set, length by length.

    python3 r6c_pisot_report.py data/r6c_pisot_class_*.txt

For each x and convention: the observed share of even j among the
near-solutions (1 <= |j| <= 30), the prediction of independent a and g,
and the prediction sum_T n_near(T) P_T(a == g) / n_near, with P_T(a == g)
from the broad set of length T (r6c_pisot_class.py). Lengths with fewer
than 20 N in the broad set use the pooled broad share.
"""
import sys
from collections import defaultdict


def main():
    for fn in sys.argv[1:]:
        rows = defaultdict(dict)
        for line in open(fn):
            if line.startswith('#'):
                continue
            f = line.split()
            x, m, T = int(f[0]), int(f[1]), f[2]
            rows[(x, m)][T] = dict(n_broad=int(f[5]), eq=float(f[8]), n_near=int(f[10]),
                                   even=float(f[11]), indep=float(f[14]), npos=int(f[15]), epos=int(f[16]))
        for (x, m), r in sorted(rows.items()):
            pooled = r['all']['eq']
            num = den = 0.0
            for T, v in r.items():
                if T == 'all' or v['n_near'] == 0:
                    continue
                p = v['eq'] if v['n_broad'] >= 20 else pooled
                num += v['n_near'] * p
                den += v['n_near']
            a = r['all']
            pred = num / den if den else float('nan')
            fac = lambda s: s / (1 - s) if s < 1 else float('inf')
            print(f"x {x} 0^0={m}: near {a['n_near']}, even share {a['even']:.3f} (factor {fac(a['even']):.2f}); "
                  f"independent {a['indep']:.3f}; broad pooled {pooled:.3f}; broad by length {pred:.3f} "
                  f"(factor {fac(pred):.2f}); j > 0 only: {a['epos']} even of {a['npos']}")


if __name__ == '__main__':
    main()
