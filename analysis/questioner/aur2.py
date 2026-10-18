import sympy, math
from sympy import Symbol, cyclotomic_poly
X=Symbol('X'); t=Symbol('t')
for x in [31,43,47,59,67,71,79]:
    if not sympy.ntheory.factor_.core(x)==x: continue
    p=sympy.expand(cyclotomic_poly(2*x,X).subs(X,x*t**2))
    fs=sympy.factor_list(p)[1]
    vals=sorted(sympy.Poly(f,t).eval(1) for f,e in fs)
    if len(vals)==2:
        print(x, float(vals[1]/vals[0]), math.e**2)
