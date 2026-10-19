"""Tables for question 83 from data/r5m_block_q*e*.txt.

Per type of B - 1: census, refined model and refined block model per base,
and both ratios. Per orbit: a Pearson statistic in units of the families of
q (q - 1) solutions (Lemma 24.8), one term per orbit representative,
sum (c - E)^2 / E over orbits with E > 0, for the refined model and the
refined block model.

usage: python3 r5m_block_report.py FILE...
"""
import re
import sys
from collections import defaultdict


def main():
    for path in sys.argv[1:]:
        q, e = map(int, re.search(r'q(\d+)e(\d+)', path).groups())
        fam = q * (q - 1)
        rows = []
        for line in open(path):
            m = re.match(r'orbit (\d+) size (\d+) k (\d+) type (.*?) census (\S+) refined (\S+) block (\S+) '
                         r'block_x_q\^k (\S+) block_res (\S+) block_res_self (\S+) block_id (\S+)', line)
            if m:
                rows.append(dict(size=int(m.group(2)), k=int(m.group(3)), type=m.group(4),
                                 c=float(m.group(5)), ref=float(m.group(6)), blk=float(m.group(9)),
                                 self=float(m.group(10))))
        print(f"# q {q} e {e}: {len(rows)} orbits")
        agg = defaultdict(lambda: [0, 0.0, 0.0, 0.0])
        for r in rows:
            a = agg[r['type']]
            a[0] += r['size']
            a[1] += r['size'] * r['c']
            a[2] += r['size'] * r['ref']
            a[3] += r['size'] * r['blk']
        print("| type of `B - 1` | bases | census | refined | block | census/refined | census/block |")
        print("|---|---:|---:|---:|---:|---:|---:|")
        tot = [0, 0.0, 0.0, 0.0]
        for ty, a in sorted(agg.items(), key=lambda kv: -kv[1][0]):
            for i in range(4):
                tot[i] += a[i]
            n = a[0]
            r1 = f"{a[1] / a[2]:.2f}" if a[2] else "-"
            r2 = f"{a[1] / a[3]:.2f}" if a[3] else "-"
            print(f"| {ty} | {n} | {a[1] / n:.2f} | {a[2] / n:.2f} | {a[3] / n:.2f} | {r1} | {r2} |")
        n = tot[0]
        print(f"| all | {n} | {tot[1] / n:.2f} | {tot[2] / n:.2f} | {tot[3] / n:.2f} | {tot[1] / tot[2]:.2f} | {tot[1] / tot[3]:.2f} |")
        for key, name in (('ref', 'refined'), ('blk', 'block')):
            chi = 0.0
            dof = 0
            for r in rows:
                E = r[key] / fam
                c = r['c'] / fam
                if E > 0:
                    chi += (c - E) ** 2 / E
                    dof += 1
                elif c > 0:
                    chi = float('inf')
            print(f"Pearson per orbit, {name}: {chi:.1f} on {dof} orbits")
        sh = sum(r['size'] * r['self'] for r in rows) / sum(r['size'] * r['blk'] for r in rows)
        print(f"share of the block model mass from the exact solutions themselves: {sh:.3f}\n")


if __name__ == '__main__':
    main()
