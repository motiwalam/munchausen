"""Round 5, families: numeric checks of the inequalities used in the proofs.

1. Theorem 1.6 (3 digits, square class): for two digits <= B and the third
   digit x >= 2B + 4, the remainder R satisfies |R| < 2 sqrt(N) - 1, where
   N = 4 * (leading digit) * x^x is the dominant term, in all three positions.
   Checked with logarithms for B = 1..400 and x from 2B + 4 to 2B + 400; the
   proof covers larger x by monotonicity.
2. rho_M = w(M-1)/w(M) = (1/M)(1 - 1/M)^(M-1) <= 1/(2M) for M >= 2, used in
   section 3, and w(d) - 2 w(d-1) >= w(d)/2 for d >= 2.

    python3 analysis/r5f_bounds.py > analysis/data/r5f_bounds.txt
"""
import math


def logw(d):
    return d * math.log(d) if d >= 1 else 0.0


def check_square_class(B):
    # worst-case |R| for each position (logs); weights of the fixed digits <= B^B
    lK = logw(max(B, 1))
    bad = []
    for x in range(2 * B + 4, 2 * B + 400):
        lx = math.log(x)
        lsqrtN_min = math.log(2) + 0.5 * (x * lx)  # sqrt(N) >= 2 x^(x/2) (leading digit >= 1)
        # last:   |R| <= 4B (2 B^B + x) + B^2
        # middle: |R| <= 4B (2 B^B + B) + x^2
        # leading: N = 4 x^(x+1), sqrt N = 2 x^((x+1)/2); |R| <= 4x (2 B^B + B) + B^2
        R_last = math.log(4 * B * (2 * math.exp(lK) + x) + B * B) if lK < 600 else math.log(8 * B) + lK + 1e-9
        R_mid = math.log(4 * B * (2 * math.exp(lK) + B) + x * x) if lK < 600 else math.log(8 * B) + lK + 1e-9
        R_lead = math.log(4 * x * (2 * math.exp(lK) + B) + B * B) if lK < 600 else math.log(8 * x * B) + lK + 1e-9
        if max(R_last, R_mid, R_lead) >= lsqrtN_min:  # |R| < sqrt(N) <= 2 sqrt(N) - 1 is what is checked
            bad.append(x)
    return bad


def main():
    print("## 1. square class: |R| < sqrt(N) for x in [2B+4, 2B+400), B = 1..400")
    worst = [(B, check_square_class(B)) for B in range(1, 401)]
    fails = [(B, b) for B, b in worst if b]
    print(f"failures: {fails[:5]} (count {len(fails)})")
    print("## 2. rho_M <= 1/(2M) and w(d) - 2 w(d-1) >= w(d)/2")
    ok = all((1 / M) * (1 - 1 / M) ** (M - 1) <= 1 / (2 * M) + 1e-15 for M in range(2, 10 ** 6))
    ok2 = all(2 * (d ** d - 2 * (d - 1) ** (d - 1)) >= d ** d for d in range(2, 200))
    print(f"rho_M <= 1/(2M) for 2 <= M < 10^6: {ok}; w(d) - 2w(d-1) >= w(d)/2 for 2 <= d < 200 (exact): {ok2}")
    print("(both follow from (1 - 1/M)^(M-1) decreasing from 1/2 at M = 2)")


if __name__ == '__main__':
    main()
