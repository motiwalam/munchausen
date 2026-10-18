import itertools, sys
def negadigits(n,b):
    out=[]
    while n:
        n,r=divmod(n,-b)
        if r<0: r+=b; n+=1
        out.append(r)
    return out
for b in range(2,int(sys.argv[1])+1):
    res={0:[],1:[]}
    for d in range(2,b+3):
        for combo in itertools.combinations_with_replacement(range(b),d):
            z=combo.count(0)
            F0=sum(x**x for x in combo if x)
            for m in (0,1):
                F=F0+m*z
                if F<=1: continue
                dg=negadigits(F,b)
                if len(dg)==d and tuple(sorted(dg))==combo:
                    res[m].append(tuple(reversed(dg)))
    print(b,len(res[0]),len(res[1]),res[0][:6],res[1][:6],flush=True)
