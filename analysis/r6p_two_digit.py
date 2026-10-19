"""Count the 2-digit strings (a, c), digits up to M, that are solutions in some base.

(a, c) is a solution exactly when a divides w(c) - c and the base
(a^a + w(c) - c) / a exceeds a and c (Proposition 2.6). Used for the
"Problems found" section of docs/library/questions-round6.md:

    python3 analysis/r6p_two_digit.py 60
"""
import sys

M = int(sys.argv[1])
tot = 0
for m in (0, 1):
    cnt = 0
    for a in range(1, M + 1):
        for c in range(M + 1):
            g = (c ** c if c > 0 else m) - c
            if (a ** a + g) % a == 0 and (a ** a + g) // a > max(a, c):
                cnt += 1
    print('0^0 = %d: %d solutions, share %.4f of the strings' % (m, cnt, cnt / (M * (M + 1))))
    tot += cnt
print('both conventions together:', tot)
