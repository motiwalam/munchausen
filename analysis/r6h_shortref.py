"""Question 91: the refined model at short lengths, computed exactly.

For every base b and length d, E_basic(b, d) and E_ref(b, d) (the refined
model of section 5.3, identity modulo b - 1) by the exact walk of
r6q_lib.py. Prints the totals of the short exceptions of section 10.5
(3 to 5 digits, J = b - d > ln b + 2, bases 10 to 41 and 43), and per
length the totals over bases with the observed counts of the census.

    python3 r6h_shortref.py > data/r6h_shortref.txt
"""
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r6q_lib as R  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))


def census():
    """(m, b) -> list of solution lengths (nontrivial, at least 2 digits)"""
    out = {}
    for m in (0, 1):
        for name in (f'b2-41-{m}.txt', f'b43-{m}.txt'):
            for line in open(os.path.join(HERE, '..', 'output', name)):
                parts = line.strip().split(':', 3)
                if len(parts) < 4:
                    continue
                b = int(parts[0])
                for s in parts[3].replace(' ', '').split('),('):
                    s = s.strip('(),')
                    if not s:
                        continue
                    d = len(s.split(','))
                    if d >= 2:
                        out.setdefault((m, b), []).append(d)
    return out


def expect(b, d, m):
    w = R.weights(b, m)
    basic = sum(p for L, _, _, _, _, p in R.leaves(b, d, w) if L == d)
    ref = float(R.refined_by_zeros(b, d, w).sum())
    return basic, max(ref, 0.0)


def main():
    obs = census()
    bases = list(range(10, 42)) + [43]
    thr = {b: math.floor(math.log(b) + 2) + 1 for b in bases}
    print("# short exceptions of section 10.5: 3..5 digits, b - d >= threshold(b), bases 10..41, 43")
    for m in (1, 0):
        eb = er = 0.0
        o = 0
        for b in bases:
            for d in (3, 4, 5):
                if b - d < thr[b]:
                    continue
                x, y = expect(b, d, m)
                eb += x
                er += y
                o += obs.get((m, b), []).count(d)
        print(f"0^0={m}: basic {eb:.3f} refined {er:.3f} observed {o}")
    print("# per length d, bases max(9, d)..41: basic, refined, ratio, observed")
    for m in (1, 0):
        for d in range(3, 13):
            eb = er = 0.0
            o = 0
            for b in range(max(9, d), 42):
                x, y = expect(b, d, m)
                eb += x
                er += y
                o += obs.get((m, b), []).count(d)
            print(f"0^0={m} d={d}: basic {eb:.3f} refined {er:.3f} ratio {er / eb:.3f} observed {o}", flush=True)


if __name__ == '__main__':
    main()
