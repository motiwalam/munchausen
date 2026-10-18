# m=1 constructions: self-paying digits + one swap (a at pos k, e at pos 0) with a*b^k = e^e, e = a^a + z
import math
def ispow(n):
    for e in range(2,64):
        r=round(n**(1/e))
        for rr in (r-1,r,r+1):
            if rr>1 and rr**e==n: return True
    return False
def w(x): return 1 if x==0 else x**x
found=[]
for r in range(2,20):
    if ispow(r): continue
    for t in range(2,200):
        b=r**t
        sp={}
        for s in range(1,t):
            if (s*(pow(r,s,t*s)-1))%t==0 and (s*(r**s-1))%t==0:
                sp[s*(r**s-1)//t]=r**s
        # swap with e = r^u (e^e = r^{u r^u}), a = r^v: a b^k = e^e -> v + t k = u r^u
        for u in range(1,t):
            e=r**u
            for v in range(0,u+1):
                a=r**v
                if a>=b: continue
                num=u*r**u - v
                if num<=0 or num%t: continue
                k=num//t
                if k<1: continue
                if a>1 and a*math.log(a) > u*math.log(r)+1: continue
                need_z = e - w(a)   # zeros needed
                if need_z<0: continue
                # choose leading self-paying position K > k (or leading is a itself at k with no sp above)
                cands=[(k,None)]+[(K,d) for K,d in sp.items() if K>k]
                for K,lead in cands:
                    L=K+1
                    # positions 1..K-1 except k hold zeros or self-paying digits; position 0 holds e
                    avail=[p for p in sp if 0<p<K and p!=k]
                    fixed_nonzero = 2 + (1 if lead is not None else 0)  # a, e, lead
                    if lead is None: fixed_nonzero=2
                    # zeros = L - fixed_nonzero - j, j chosen from avail
                    j = L - fixed_nonzero - need_z
                    if 0<=j<=len(avail) and e<b:
                        found.append((r,t,b if b<10**12 else f"{r}^{t}",'a',a,'k',k,'e',e,'K',K,'j',j,len(avail)))
print(len(found))
for f in found[:40]: print(f)
