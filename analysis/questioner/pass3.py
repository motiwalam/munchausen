import math
from sympy import primerange, legendre_symbol
P=list(primerange(2,62))
def w(x,m): return m if x==0 else x**x
M=80; m=1
tot=0; sq=0; nsq=[]
for a in range(1,M+1):
  for b1 in range(M+1):
    for c in range(M+1):
      F=w(a,m)+w(b1,m)+w(c,m)
      A,B,C=a,b1,c-F
      ok=True
      for p in P:
        # root mod p?
        if not any((A*r*r+B*r+C)%p==0 for r in range(p)): ok=False;break
      if ok:
        tot+=1
        D=B*B-4*A*C
        r=math.isqrt(D) if D>=0 else -1
        if r*r==D: sq+=1
        else: nsq.append((a,b1,c))
print(tot,sq,len(nsq),nsq[:20])
