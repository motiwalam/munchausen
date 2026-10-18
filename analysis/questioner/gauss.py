import itertools, sys
def w(x,m): return m if x==0 else x**x
n=int(sys.argv[1]); L=int(sys.argv[2])
beta=complex(-n,1)
D=n*n+1
res={0:[],1:[]}
# exact arithmetic with Gaussian ints as pairs
def mul(a,b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
pw=[(1,0)]
for i in range(L): pw.append(mul(pw[-1],(-n,1)))
for k in range(2,L+1):
  for s in itertools.product(range(n*n+1),repeat=k):
    if s[0]==0: continue
    re=sum(s[j]*pw[k-1-j][0] for j in range(k)); im=sum(s[j]*pw[k-1-j][1] for j in range(k))
    if im!=0: continue
    for m in (0,1):
      if re==sum(w(x,m) for x in s): res[m].append(s)
for m in (0,1): print(n,m,len(res[m]),res[m][:20])
