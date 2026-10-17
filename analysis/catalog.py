"""One catalog of every Munchausen number found so far.

Sources:
- output/b2-41-*.txt: exhaustive, bases 2-41;
- data/b39-127-d30.txt: every solution with at most 30 digits, bases 39-127;
- data/k<k>.txt: every k-digit solution in every base up to a bound (k <= 6).

Each entry is (mode, base, digits). Trivial solutions (0 and 1) are left out.
"""
import glob
import os

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..')


def _load_lines(path):
    out = []
    for line in open(path):
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        b, m, n, ns = line.split(':', 3)
        for t in (eval('(' + ns + ',)') if ns.strip() else ()):
            if t not in ((0,), (1,)):
                out.append((int(m), int(b), tuple(t)))
    return out


def exhaustive_bases():
    """Bases searched completely, with their solutions per convention."""
    sols = {}
    files = [os.path.join(ROOT, 'output', f'b2-41-{m}.txt') for m in (0, 1)]
    for f in files:
        for m, b, t in _load_lines(f):
            sols.setdefault((m, b), set()).add(t)
        for line in open(f):
            if line.strip():
                b, m = line.split(':')[:2]
                sols.setdefault((int(m), int(b)), set())
    return sols


def short_solutions():
    return _load_lines(os.path.join(HERE, 'data', 'b39-127-d30.txt'))


def kdigit_solutions():
    out = []
    for f in sorted(glob.glob(os.path.join(HERE, 'data', 'k[0-9].txt'))):
        for line in open(f):
            if line.startswith('#') or not line.strip():
                continue
            k, m, b, s = line.split()
            out.append((int(m), int(b), tuple(map(int, s.split(',')))))
    return out


def everything():
    seen = set()
    for (m, b), ts in exhaustive_bases().items():
        for t in ts:
            seen.add((m, b, t))
    seen.update(short_solutions())
    seen.update(kdigit_solutions())
    return sorted(seen, key=lambda e: (e[1], e[0], len(e[2]), e[2]))


if __name__ == '__main__':
    allsol = everything()
    print(len(allsol), "nontrivial solutions in the catalog")
    print("exhaustive bases:", sorted({b for (m, b) in exhaustive_bases()})[-1])
