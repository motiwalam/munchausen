import math, itertools, sys
def w(x,m): return m if x==0 else x**x
# negabase 3-digit: s2 c^2 - s1 c + s0 = F, c > max(s)
M=int(sys.argv[1])
for m in (0,1):
  out=[]
  for s2 in range(1,M+1):
    for s1 in range(0,M+1):
      for s0 in range(0,M+1):
        F=w(s2,m)+w(s1,m)+w(s0,m)
        # s2 c^2 - s1 c + (s0-F)=0
        D=s1*s1-4*s2*(s0-F)
        if D<0: continue
        r=math.isqrt(D)
        if r*r!=D: continue
        if (s1+r)%(2*s2): continue
        c=(s1+r)//(2*s2)
        if c>max(s2,s1,s0):
          out.append((c,(s2,s1,s0)))
  out.sort()
  # filter trivial self-paying-like with s1==0 for m=0
  print(m,len(out),[o for o in out if not (m==0 and o[1][1]==0)][:40])
