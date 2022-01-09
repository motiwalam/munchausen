#!/usr/bin/env python3.10

# --------- utility functions ----------

# reads a file where each line contains information in the format specified above
# returns a tuple of 3-tuples: (base, mode, number of numbers, numbers)
def readf(fn):
    out = ()
    with open(fn) as fh:
        for l in fh.readlines():
            b,m,n,ns = l.strip().split(':')
            b,m,n = map(int, (b,m,n))
            ns  = () if not ns else eval(f"({ns},)")
            out += (b,m,n,ns),

    return out

# converts a vector digits to a string
# all it does is take all digits greater than 10 and wrap them
# in square brackets
# thus (1,10,15,8,3,4,19) -> 1[10][15]834[19]
tostr = lambda v: ''.join(map(lambda c: str(c) if c<10 else f'[{c}]', v))

# converts above representation back to vector of digits
fromstr = lambda s: () if not s else (int(s[0]),) + fromstr(s[1:]) if s[0]!='[' else (int(s[1:s.index(']')]),) + fromstr(s[s.index(']')+1:])