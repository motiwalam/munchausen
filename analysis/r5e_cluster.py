"""Round 5, question 73: group near-solutions into clusters.

Two events (b, m, D, digits) are in one cluster when
- they have the same digit multiset (the swap lemma), or
- they have the same base, convention and offset and their values differ
  by w(y) - w(x) = y - x with the last digit x replaced by y, which is the
  twin rule (0^0 = 0: last digits 0 and 1; factorions with w(0) = 0:
  last digits 0, 1, 2; factorions with w(0) = 1: last digits 1, 2).

    load_events(path, fmt) -> list of events
    clusters(events, twins) -> list of cluster ids, aligned with events

Formats: 'r5e' (hit b m k digits, from r5e_int_offsets.py) and 'fact'
(off b j m count digits..., from r2c_fact_offsets.py).
"""
from collections import defaultdict


def load_r5e(path):
    ev, done = [], defaultdict(set)
    for line in open(path):
        p = line.split()
        if not p:
            continue
        if p[0] == 'hit':
            ev.append((int(p[1]), int(p[2]), int(p[3]), tuple(map(int, p[4].split(',')))))
        elif p[0] == 'done':
            done[int(p[1])].add(int(p[2]))
    return ev, done


def load_fact(path):
    ev, done = [], defaultdict(set)
    for line in open(path):
        p = line.split()
        if not p or p[0] != 'off':
            continue
        b, j, m, cnt = int(p[1]), int(p[2]), int(p[3]), int(p[4])
        done[b].add(j)
        strs = p[5:]
        assert len(strs) == cnt, line
        for s in strs:
            ev.append((b, m, j, tuple(map(int, s.split(',')))))
    return ev, done


class UF:
    def __init__(self, n):
        self.p = list(range(n))

    def find(self, x):
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x

    def union(self, a, b):
        a, b = self.find(a), self.find(b)
        if a != b:
            self.p[a] = b


def clusters(events, twin_digits):
    """twin_digits(m) -> set of last digits that form twins under m."""
    uf = UF(len(events))
    by_ms = {}
    by_prefix = {}
    for i, (b, m, k, s) in enumerate(events):
        key = (b, m, tuple(sorted(s)))
        if key in by_ms:
            uf.union(i, by_ms[key])
        else:
            by_ms[key] = i
        if s[-1] in twin_digits(m):
            pk = (b, m, k, s[:-1])
            if pk in by_prefix:
                uf.union(i, by_prefix[pk])
            else:
                by_prefix[pk] = i
    return [uf.find(i) for i in range(len(events))]


def twins_pow(m):
    return {0, 1} if m == 0 else set()


def twins_fact(m):
    return {0, 1, 2} if m == 0 else {1, 2}
