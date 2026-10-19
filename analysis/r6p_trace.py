"""Length-transition matrix of the basic model, and its trace and spectrum.

M[d, d'] is the chance that F of a uniform d-digit string (nonzero leading
digit, 0^0 = 1) has d' digits. The basic model's expected count over the
lengths 1 to b is trace(M). Lead for question 90 of
docs/library/questions-round6.md. Needs numpy (the venv of chapter 27):

    ~/.local/share/venvs/munchausen/bin/python analysis/r6p_trace.py 40 20000
"""
import sys
import numpy as np

b = int(sys.argv[1])
N = int(sys.argv[2])
rng = np.random.default_rng(1)
lnb = np.log(b)
x = np.arange(b, dtype=float)
lw = np.where(x > 0, x * np.log(np.maximum(x, 1)), 0.0)  # ln w(x), w(0) = 1
scale = (b - 1) * np.log(b - 1)
wr = np.exp(lw - scale)  # w(x) / w(b-1), so that sums stay in range
M = np.zeros((b + 1, b + 1))
for d in range(1, b + 1):
    first = rng.integers(1, b, size=N)
    s = wr[first]
    if d > 1:
        s = s + wr[rng.integers(0, b, size=(N, d - 1))].sum(axis=1)
    L = np.floor((np.log(s) + scale) / lnb + 1e-12).astype(int) + 1
    L = np.clip(L, 1, b)
    for length, c in zip(*np.unique(L, return_counts=True)):
        M[d, length] += c / N
M = M[1:, 1:]
ev = sorted(np.linalg.eigvals(M), key=lambda z: -abs(z))
print('b %d  trace %.4f  (length 1 alone %.4f)' % (b, np.trace(M), M[0, 0]))
print('diagonal at d = b, b-1, ..., b-5:', ' '.join('%.4f' % M[b - 1 - j, b - 1 - j] for j in range(6)))
print('largest eigenvalues:', ' '.join('%.4f' % abs(z) for z in ev[:5]))
print('sum of the eigenvalues other than 1: %.4f' % sum(ev[1:]).real)
