"""Question 75: how often the optimal adaptive tree of r5l_cert.py reveals the largest unrevealed value.

Ties go to the larger value. Prints b, the certificate size, the internal nodes
of the optimal tree, and how many of them branch on the largest unrevealed value.
"""
import sys
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from functools import lru_cache
from r5l_cert import Inst, make_weights
for b in range(5, 11):
    inst = Inst(b, b - 1, make_weights(b, 'true', 1, 1))
    vals = inst.vals
    @lru_cache(maxsize=None)
    def opt(R):
        if inst.fails(R) or inst.is_singleton(R):
            return 1, None
        rv = {v for v, _ in R}
        rf = inst.d - sum(k for _, k in R)
        best = None
        for v in sorted((v for v in vals if v not in rv), reverse=True):
            tot = sum(opt(tuple(sorted(R + ((v, e),))))[0] for e in range(rf + 1))
            if best is None or tot < best[0]:
                best = (tot, v)
        return best
    # walk the optimal tree and count the nodes whose choice is the largest unrevealed value
    tot = top = 0
    stack = [()]
    while stack:
        R = stack.pop()
        c, v = opt(R)
        if v is None:
            continue
        rv = {x for x, _ in R}
        tot += 1
        if v == max(x for x in vals if x not in rv):
            top += 1
        rf = inst.d - sum(k for _, k in R)
        for e in range(rf + 1):
            stack.append(tuple(sorted(R + ((v, e),))))
    print(b, opt(())[0], 'internal nodes', tot, 'choose the largest unrevealed value', top, f'{top/tot:.2f}', flush=True)
    opt.cache_clear()
