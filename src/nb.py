#!/usr/bin/env python3.10

from math import ceil
from functools import reduce
from itertools import takewhile, count, product

# ------- combinatoric functions ---------
# factorial
fact = lambda n: reduce(lambda a,b:a*b, range(1,n+1),1)
# combinations
ncr  = lambda n,r: fact(n)/(fact(r)*fact(n-r))
# combinations with repetition
ncrr = lambda n,r: ncr(n+r-1,r)

# first number x such that x^x is greater than n
fm = lambda n: max(takewhile(lambda x:x**x<n, count()), default=0)+1

# -------- search space calculation functions ---------

# 1-digit numbers are constant time since its always 1 and 0 (if 0^0=0 convention is adopted)

# naively iterate over all possible numbers
nb0 = lambda b: 2*b**b

# using combinations of digits
nb1 = lambda b: sum(ncrr(b,d) for d in range(2,b+2))

# recognizing that (b+1) digit numbers in the search space
# all start with the digit 1
nb2 = lambda b: sum(ncrr(b,d) for d in range(2,b+1)) + ncrr(b,b)

# for a d-digit number, b**d is the largest possible value
# if a digit x in range(b) is such that x**x is greater than b**d
# then that digit can not possibly be included in a d-digit
# munchausen number
nb3 = lambda b: sum(ncrr(fm(b**d), d) for d in range(2,b+1)) + ncrr(b,b)

# (b+1) digit numbers are actually impossible, so don't need to be considered at all
nb4 = lambda b: sum(ncrr(fm(b**d), d) for d in range(2,b+1))

# a b-digit number must contain 3 copies of the digit (b-1) for b>2
nb5 = lambda b: sum(ncrr(fm(b**d), d) for d in range(2,b)) + ncrr(fm(b**(b-3)),b-3)

# applying the same logic as above for all number of digits
# a d-digit number in base b must contain a digit greater than or equal to t
# where t is the first digit x such that x^x is greater than b^(d-1)/d
# this is because d*(t-1)^(t-1) is less than b^(d-1) which is the minimum
# d-digit number.
# as an example, consider 3-digit numbers in base 10
# the minimum 3-digit number is 100
# even with all 3's, the munchausen sum is 81, so there
# needs to be at least 1 digit that is 4 or greater
# we then divide 100/(4^4) and take the ceil to see
# how many 4's are absolutely necessary. in this case
# it is one, but it may be greater.
def nb6(b):
    s = 0
    for d in range(2,b+1):
        t = fm(b**(d-1)/d)
        for r in range(t, fm(b**d)):
            n = 0 if b==2 else ceil(b**(d-1)/(r**r))
            s += ncrr(fm(b**d),d-n)

    return s


# not currently proven
# based on the conjecture that b-digit munchausen numbers are impossible for b>2
# def nb7(b):
#     s = 0
#     for d in range(2,b):
#         t = fm(b**(d-1)/d)
#         for r in range(t, fm(b**d)):
#             n = 0 if b==2 else ceil(b**(d-1)/(r**r))
#             s += ncrr(fm(b**d),d-n)

#     return s

# all nb functions
anb = tuple(map(lambda k: globals()[k], sorted(filter(lambda c: c.startswith('nb'), globals().keys()), key=lambda k: int(k[2:]))))
li  = len(anb)

# ratio functions, comparing nb{i} to nb{j}
ra = {f"{i}/{j}": (lambda b,i=i,j=j: anb[i](b)/anb[j](b)) for i,j in product(range(li),repeat=2)}

# give the search space for a base for all nb's from 0 to latest
prog = lambda b: {i:anb[i](b) for i in range(li)}
# give the ratios of search spaces for a base, showing progressive improvements
rprog = lambda b: {f"{i}/{i-1}":ra[f'{i}/{i-1}'](b) for i in range(1, li)}

# give the search spaces for all bases from b2 to b1 using nb_j
ss = lambda b1,b2=2,j=li-1: {b:anb[j](b) for b in range(b2,b1+1)}
# compare the search spaces for all bases from b2 to b1 using nb_j
ssr = lambda b1,b2=3,j=li-1: {f"{b}/{b-1}":anb[j](b)/anb[j](b-1) for b in range(b2,b1+1)}

# total progress, dividing by nb1 since that is usually a more useful indicator
tp = ra[f'{li-1}/1']
latest = anb[li-1]