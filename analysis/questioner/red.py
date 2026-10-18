import itertools, sympy, sys, time
from sympy import Poly, Symbol
r=Symbol('r')
def w(x,m): return m if x==0 else x**x
k=int(sys.argv[1]); M=int(sys.argv[2]); m=1
t=time.time(); cnt={}; ex=[]
for s in itertools.product(range(M+1),repeat=k):
    if s[0]==0: continue
    F=sum(w(x,m) for x in s)
    coeffs=list(s); coeffs[-1]-=F
    P=Poly(coeffs,r)
    fl=P.factor_list()[1]
    degs=tuple(sorted(f.degree() for f,e in fl for _ in range(e)))
    cnt[degs]=cnt.get(degs,0)+1
    if degs!=(k-1,) and len(ex)<30: ex.append((s,degs,[str(f.as_expr()) for f,e in fl]))
print(cnt, time.time()-t)
for e in ex: print(e)
