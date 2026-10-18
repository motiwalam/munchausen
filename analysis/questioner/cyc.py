import itertools, sys
from collections import Counter
def run(b,m):
    W=[m]+[x**x for x in range(1,b)]
    def ms(n):
        c=[0]*b
        while n: n,r=divmod(n,b); c[r]+=1
        return tuple(c)
    # all multisets of up to b digits (as count tuples, leading digit nonzero ensured by n>0)
    # map multiset -> multiset of F
    cache={}
    def f(c): 
        s=sum(W[x]*c[x] for x in range(b))
        return ms(s) if s>0 else None
    seen_cycles=set()
    # start from every multiset with total<=b and at least one nonzero digit
    def gen(total):
        for combo in itertools.combinations_with_replacement(range(b),total):
            c=[0]*b
            for x in combo: c[x]+=1
            if sum(c[1:])>0: yield tuple(c)
    state={}
    for d in range(1,b+1):
        for c in gen(d):
            path=[];x=c
            while x is not None and x not in state and x not in path:
                path.append(x); x=f(x)
            if x is None: res=None
            elif x in state: res=state[x]
            else:
                i=path.index(x); cyc=path[i:]
                key=min(cyc); res=(key,len(cyc)); seen_cycles.add(res)
            for y in path: state[y]=res
    return sorted(l for k,l in seen_cycles)
for b in range(3,int(sys.argv[1])+1):
    for m in (0,1):
        print(b,m,Counter(run(b,m)))
