#!/usr/bin/env python3.10

from itertools import takewhile, count
from functools import reduce
from math import ceil
# common functions used across multiple modules

# encode n in base b
E = lambda n,b: () if n==0 else E(n//b,b) + (n%b,)

# decode v from base d (v is a vector of digits)
D = lambda v,b: 0 if not v else v[-1] + b*(D(v[:-1], b))

# first number x such that x^x is greater than n
fm = lambda n: max(takewhile(lambda x:x**x<n, count()), default=0)+1

# next number with all digits less than m
def nv(v, m):
    vc = list((0,) + v)
    for i in range(len(vc)-1, 0, -1):
        if vc[i] >= m:
            vc[i] = 0
            vc[i-1] += 1

    return vc[vc[0]==0:]


# ------ preemptive testing functions -------
# preemptively rule out/in a d-digit number in base-b
# mx is exclusive upperbound for digits
# mn and n are specify minimum n*mn^n > b**(d-1)
# these values are precomputed because mx-mn is not
# always 1, meaning one needs to iterate from mn to mx
# for all possible "minimum" digits
# since these are expected to be computed already in gcwr and nb
# they are passed in as arguments here

# n*m^n gives a minimum number
# if the next number with all digits less than mx has
# more than d-digits, we can rule it out
testbd0 = lambda b,d,mx,mn,n: len(nv(E(n*mn**mn, b), mx)) == d

# all testbd functions
atbd = tuple(map(lambda k: globals()[k], sorted(filter(lambda c: c.startswith('testbd'), globals().keys()), key=lambda k: int(k[6:]))))
li = len(atbd) - 1

# exported tbd function for use in munchausen
tbd = atbd[li]

# a wrapper around tbd that does not require precomputed values
# returns a list of tuples (r,n,True|False)
# where r and n are values s.t n*r^r > b^(d-1)
def wtbd(b, d):
    out = []
    t = fm(b**(d-1)/d)
    mx = fm(b**d)

    for r in range(t, mx):
        n = 0 if b==2 else ceil(b**(d-1)/(r**r))
        out.append((r, n, tbd(b,d,mx,r,n)))

    return out


wtb = lambda b: reduce(lambda a, b: a+b, (tuple((d,) + c for c in wtbd(b, d)) for d in range(2, b+1)))