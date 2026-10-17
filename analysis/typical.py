"""How big is the tree if nodes with too many large digits are dropped?

Not a valid search. It measures how the typical part of the tree scales.
"""
import sys
from tree import Tree


class Capped(Tree):
    def __init__(self, b, d, slack):
        super().__init__(b, d)
        self.slack = slack

    def rec(self, k, cnt, t, rf, occ):
        if self.slack is not None and sum(cnt.values()) > (self.b - k) * self.d / self.b + self.slack:
            return
        super().rec(k, cnt, t, rf, occ)


for b in range(16, int(sys.argv[1]) + 1):
    row = []
    for slack in (2, 4, 8, None):
        tr = Capped(b, b - 1, slack).run()
        row.append(sum(tr.nodes.values()))
    print(b, row, flush=True)
