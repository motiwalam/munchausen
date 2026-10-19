"""Question 81: the length shares of the basic model (Theorem 1.1 of round5-model.md).

s_j = lim E_(b-j): s_0 = e^-1 sum_{k>=3} 1/k!, and for j >= 1
s_j = e^-j sum_{1<=k<e^j} 1/k! + e^-(j+1) sum_{k>e^(j+1)} 1/k!.

E_(b-j) at finite b from the exact law of the top counts: with y0 the
smallest y with a digit b - y present and k its count, the string has
b - j digits exactly when (y0 = j and k w(b-j) < b^(b-j)) or
(y0 = j + 1 and k w(b-j-1) >= b^(b-j-1)). For b >= b_0(j) this is exact up to
the tail events of Lemma 1.4. A Monte Carlo of the model itself
(analysis/model.py) checks it.

usage: python3 r5m_shares.py [mc_samples]
"""
import math
import sys

sys.path.insert(0, __file__.rsplit('/', 1)[0])


def s_limit(j, kmax=200):
    f = [1.0]
    for k in range(1, kmax + 1):
        f.append(f[-1] / k)
    if j == 0:
        return math.exp(-1) * sum(f[3:])
    a = math.exp(-j) * sum(f[k] for k in range(1, kmax + 1) if k < math.exp(j))
    b = math.exp(-(j + 1)) * sum(f[k] for k in range(1, kmax + 1) if k > math.exp(j + 1))
    return a + b


def p_top(b, d, y, k):
    """P(no digit above b - y, exactly k copies of b - y) for a d-digit string,
    leading digit uniform on 1..b-1, the others uniform on 0..b-1"""
    n = d - 1

    def lb(nn, kk, extra):
        if kk < 0 or kk > nn:
            return 0.0
        return math.exp(math.lgamma(nn + 1) - math.lgamma(kk + 1) - math.lgamma(nn - kk + 1)
                        - kk * math.log(b) + (nn - kk) * math.log(1 - y / b)) * extra
    return lb(n, k, (b - 1 - y) / (b - 1)) + lb(n, k - 1, 1 / (b - 1))


def lw(x):
    return x * math.log(x)


def e_exact(b, j):
    d = b - j
    tot = 0.0
    if j >= 1:
        # y0 = j: length b - j iff k w(b-j) < b^(b-j)
        thr = math.exp((b - j) * math.log(b) - lw(b - j))
        k = 1
        while k < thr:
            tot += p_top(b, d, j, k)
            k += 1
    # y0 = j + 1: length b - j iff k w(b-j-1) >= b^(b-j-1)
    thr = math.exp((b - j - 1) * math.log(b) - lw(b - j - 1))
    k = max(1, math.ceil(thr))
    while k <= d:
        p = p_top(b, d, j + 1, k)
        tot += p
        if p < 1e-18 and k > thr + 5:
            break
        k += 1
    return tot


def c_first(j, kmax=200):
    """first-order coefficient: E_(b-j) = s_j + c_j / b + O(1/b^2) (Proposition 1.6)"""
    def delta(y, k):
        return (j + 1) * (y - k) + y * k + k - k * (k - 1) / 2 - y * y / 2 - y
    tot = 0.0
    f = [1.0]
    for k in range(1, kmax + 1):
        f.append(f[-1] / k)
    for k in range(1, kmax + 1):
        if j >= 1 and k < math.exp(j):
            tot += math.exp(-j) * f[k] * delta(j, k)
        if k > math.exp(j + 1):
            tot += math.exp(-(j + 1)) * f[k] * delta(j + 1, k)
    return tot


def main():
    mc = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    J = 6
    s = [s_limit(j) for j in range(J)]
    print("first-order coefficients c_j:", ' '.join(f"{c_first(j):+.4f}" for j in range(J)))
    print("limit shares s_j:", ' '.join(f"{x:.6f}" for x in s), " rest", f"{1 - sum(s):.6f}")
    print("second term of s_1 (y0 = 2, k >= 8):", f"{math.exp(-2) * sum(1 / math.factorial(k) for k in range(8, 40)):.3e}")
    print("\nb | E_b E_(b-1) ... E_(b-5) (exact top-count formula) | b * (E - s) for j = 0..5")
    for b in (30, 100, 300, 1000, 3000, 10000, 100000):
        e = [e_exact(b, j) for j in range(J)]
        print(f"{b} | " + ' '.join(f"{x:.5f}" for x in e) + " | " + ' '.join(f"{b * (x - y):+.3f}" for x, y in zip(e, s)))
    if mc:
        import model
        print(f"\nMonte Carlo of analysis/model.py, {mc} samples (mean, standard error):")
        for b in (30, 100):
            row = [model.expected(b, b - j, 0, mc) for j in range(4)]
            print(f"b {b}: " + ' '.join(f"{p:.4f}+-{se:.4f} (formula {e_exact(b, j):.4f})" for j, (p, se) in enumerate(row)))


if __name__ == '__main__':
    main()
