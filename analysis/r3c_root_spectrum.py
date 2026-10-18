"""Questions 48 and 49: the root heuristic of section 11.4, with offsets and
with p-adic local factors.

For a k-digit string s and an offset D, Q_{s,D}(r) = P_s(r) - F(s) - D. The
heuristic gives the string the weight

    min(1, S / P_s'(b*)),

where b* > max(s) is the real root of P_s(b) = F(s) + D, and S is a product
of local factors. Three choices of S:

    plain   S = 1
    prime   S = prod_{p <= 31} rho(p), rho(p) = #roots of Q_{s,D} mod p
            (this is analysis/root_local.py)
    padic   as prime, but for p = 2, 3, 5 the count of roots mod 2^6, 3^4
            and 5^3 in place of rho(p)

The count of roots mod p^e is the local density of the event p^e | Q(b) for a
random integer b, relative to a random value, so it is the p-adic factor of
the singular series. It equals rho(p) when every root mod p is simple, and
it averages exactly 1 over a uniform constant term for every e.

The script sums the weights over all strings with digits up to X and prints
one line per offset and convention.

    python3 r3c_root_spectrum.py k X D1,D2,... [q2,q3,q5] > data/r3c_root_spectrum_k<k>.txt
    D can be written as a range a:b (step 1) or a:b:c. The optional last
    argument replaces the moduli 64,81,125 of the p-adic factors.

Output lines: k X D mode strings plain prime padic avgprime avgpadic, where
the averages are those of S over the strings that have a real root.
"""
import sys
import numpy as np

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
PADIC = {2: 64, 3: 81, 5: 125}
CHUNK = 20000
# ranges of the real root b* for the split of the sums
BINS = [(0, 10), (10, 100), (100, float('inf'))]


def strings(k, X):
    g = np.indices((X + 1,) * k).reshape(k, -1).T
    return g[g[:, 0] >= 1].astype(np.int64)


def hist(S, q):
    """h[i, v] = number of r mod q with P_s(r) = v mod q, as uint8."""
    n, k = S.shape
    h = np.zeros((n, q), dtype=np.uint8)
    r = np.arange(q, dtype=np.int64)
    for a in range(0, n, CHUNK):
        Sc = S[a:a + CHUNK]
        v = np.zeros((len(Sc), q), dtype=np.int64)
        for j in range(k):
            v = (v * r + Sc[:, j:j + 1]) % q
        idx = (np.arange(len(Sc))[:, None] * q + v).ravel()
        h[a:a + CHUNK] = np.bincount(idx, minlength=len(Sc) * q).reshape(len(Sc), q).astype(np.uint8)
    return h


class Strings:
    def __init__(self, k, X):
        self.k, self.X = k, X
        self.S = strings(k, X)
        self.mx = self.S.max(axis=1)
        self.h = {q: hist(self.S, q) for q in PRIMES + list(PADIC.values())}
        self.Ff = {}
        self.Fq = {}
        for mode in (0, 1):
            wf = np.array([float(mode) if x == 0 else float(x) ** x for x in range(X + 1)])
            self.Ff[mode] = wf[self.S].sum(axis=1)
            for q in self.h:
                wq = np.array([mode % q if x == 0 else pow(x, x, q) for x in range(X + 1)], dtype=np.int64)
                self.Fq[mode, q] = wq[self.S].sum(axis=1) % q
        # zero-free strings give the same equation under both conventions
        self.zeros = (self.S == 0).sum(axis=1)

    def P(self, b):
        v = np.zeros_like(b)
        dv = np.zeros_like(b)
        for j in range(self.k):
            dv = dv * b + v
            v = v * b + self.S[:, j]
        return v, dv

    def root(self, T):
        """real root b* > max(s) of P_s(b) = T, NaN if there is none"""
        lo = self.mx + 1.0
        plo, _ = self.P(lo)
        ok = plo <= T
        b = np.maximum((T / self.S[:, 0]) ** (1.0 / (self.k - 1)), lo)
        for _ in range(200):
            v, dv = self.P(b)
            nb = np.maximum(b - (v - T) / dv, lo)
            if np.all(np.abs(nb - b) <= 1e-12 * b):
                b = nb
                break
            b = nb
        b[~ok] = np.nan
        return b

    def run(self, D, mode):
        T = self.Ff[mode] + D
        b = self.root(T)
        has = ~np.isnan(b)
        _, dv = self.P(np.where(has, b, 1.0))
        n = len(self.S)
        ar = np.arange(n)
        sp = np.ones(n)
        sa = np.ones(n)
        for q in PRIMES:
            c = (self.Fq[mode, q] + D) % q
            rho = self.h[q][ar, c].astype(float)
            sp *= rho
            if q in PADIC:
                Q = PADIC[q]
                cQ = (self.Fq[mode, Q] + D) % Q
                sa *= self.h[Q][ar, cQ].astype(float)
            else:
                sa *= rho
        plain = np.where(has, np.minimum(1.0, 1.0 / dv), 0.0)
        prime = np.where(has, np.minimum(1.0, sp / dv), 0.0)
        padic = np.where(has, np.minimum(1.0, sa / dv), 0.0)
        bins = []
        bb = np.where(has, b, 0.0)
        for lo, hi in BINS:
            sel = (bb >= lo) & (bb < hi)
            bins += [prime[sel].sum(), padic[sel].sum()]
        return (int(has.sum()), plain.sum(), prime.sum(), padic.sum(), sp[has].mean(), sa[has].mean(), bins)


def parse(spec):
    out = []
    for part in spec.split(','):
        if ':' in part:
            a = list(map(int, part.split(':')))
            out += list(range(a[0], a[1] + 1, a[2] if len(a) > 2 else 1))
        else:
            out.append(int(part))
    return out


def main():
    k, X = int(sys.argv[1]), int(sys.argv[2])
    Ds = parse(sys.argv[3])
    if len(sys.argv) > 4:
        PADIC.update(zip((2, 3, 5), map(int, sys.argv[4].split(','))))
    st = Strings(k, X)
    print(f"# k={k} X={X}: {len(st.S)} strings; p-adic moduli {sorted(PADIC.values())}; columns: k X D mode strings_with_root plain prime padic avg_prime avg_padic, "
          f"then prime and padic for b* < 10, 10 <= b* < 100, b* >= 100", flush=True)
    for D in Ds:
        for mode in (1, 0):
            n, pl, pr, pa, ap, aa, bins = st.run(D, mode)
            print(f"{k} {X} {D} {mode} {n} {pl:.4f} {pr:.4f} {pa:.4f} {ap:.4f} {aa:.4f} " + ' '.join(f"{v:.4f}" for v in bins), flush=True)


if __name__ == '__main__':
    main()
