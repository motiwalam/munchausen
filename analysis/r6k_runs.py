"""Round 6, k-length: inputs for r6k_sieve and the exact check of survivors.

usage:
  r6k_runs.py census K B X         every k-digit family with K - 1 small
                                   digits <= B and one digit x <= X, every
                                   position, both conventions where a small
                                   digit is 0; the self-paying leading
                                   families (x, 0, ..., 0) and
                                   (x, 0, ..., 0, 1) under 0^0 = 0 are left
                                   out (they have infinitely many solutions)
  r6k_runs.py thue B FILE          the binomial families of Theorem K.4:
                                   (p, q, r, x) with q^2 = 3pr, p not a cube,
                                   p, q, r <= B, x == 0 mod 3 up to the bound
                                   X_T in FILE (output of r6k_thue_bound.gp)
  r6k_runs.py check FILE           decide every survivor in FILE

Sieve input lines:  k j m x0 x1 M a d_1 ... d_(k-1)
"""
import math
import sys

sys.set_int_max_str_digits(0)


def w(d, m):
    return m if d == 0 else d ** d


def conventions(digits):
    return (0, 1) if 0 in digits else (1,)


def census(K, B, X):
    import itertools
    for j in range(K):
        for ds in itertools.product(range(B + 1), repeat=K - 1):
            if j < K - 1 and ds[0] == 0:
                continue  # the leading digit is small and must be >= 1
            for m in conventions(ds):
                if j == K - 1 and m == 0 and all(d == 0 for d in ds[:-1]) \
                        and ds[-1] in (0, 1):
                    continue
                print(K, j, m, 1, X, 1, 0, *ds)


def thue(B, path):
    bounds = {}
    for line in open(path):
        if line.startswith("#"):
            continue
        f = line.split()
        p, q, r, m = map(int, f[:4])
        bounds[(p, q, r, m)] = max(float(f[9]), float(f[10]), float(f[11]))
    for (p, q, r, m), X in sorted(bounds.items()):
        if max(p, q, r) <= B:
            print(4, 0, m, 3, int(math.ceil(X)), 3, 0, p, q, r)


def digits_of(k, j, ds, x):
    ix = k - 1 - j
    s = list(ds)
    s.insert(ix, x)
    return s


def solve(s, m):
    """Exact test: the base b > max(s) with P_s(b) = F(s), or None."""
    F = sum(w(d, m) for d in s)
    k = len(s)

    def P(b):
        v = 0
        for d in s:
            v = v * b + d
        return v

    # P is increasing for b >= 1; bracket the root
    lo = 1
    hi = 2
    while P(hi) <= F:
        hi *= 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if P(mid) <= F:
            lo = mid
        else:
            hi = mid
    if P(lo) == F and lo > max(s):
        return lo
    return None


def check(path):
    for line in open(path):
        if not line.startswith("survivor"):
            continue
        f = line.split()
        k, j, m = int(f[1]), int(f[2]), int(f[3])
        ds = list(map(int, f[4:4 + k - 1]))
        x = int(f[4 + k - 1])
        s = digits_of(k, j, ds, x)
        if x * math.log10(max(x, 2)) > 60000:
            print(line.strip(), "-> too large for the exact test", s)
            continue
        b = solve(s, m)
        if b is None:
            print(line.strip(), "-> not a solution", s)
        else:
            print(line.strip(), "-> solution", s, "base",
                  b if b < 10 ** 30 else "of %d digits" % len(str(b)))


def main():
    cmd = sys.argv[1]
    if cmd == "census":
        census(int(sys.argv[2]), int(sys.argv[3]), int(float(sys.argv[4])))
    elif cmd == "thue":
        thue(int(sys.argv[2]), sys.argv[3])
    elif cmd == "check":
        check(sys.argv[2])


if __name__ == "__main__":
    main()
