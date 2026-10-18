from sympy import factorint, cyclotomic_poly, Symbol, factor, sqrt
import math
for x in [3,7,11,15,19,23]:
    N=x**x+1
    # (1,x,1): b(b+x)=x^x+1
    D=x*x+4*N
    r=math.isqrt(D)
    print(x, 'square' if r*r==D else 'no', 'b(b+x) closest: b~',(r-x)//2)
# Aurifeuillian factors of x^x+1 for x = 3 mod 4 squarefree: Phi_{2x}(x) = L*M
import sympy
X=Symbol('X')
for x in [3,7,11,19,23]:
    # Aurifeuillian: Phi_{2x}(x) splits since x*x^{x-1} ... compute via factoring polynomial Phi_{2x}(x*t^2) in t
    t=Symbol('t')
    p=sympy.expand(cyclotomic_poly(2*x,X).subs(X,x*t**2))
    fs=sympy.factor_list(p)
    vals=[sympy.Poly(f,t).eval(1) for f,e in fs[1]]
    print(x, [len(str(v)) for v in vals], vals if x<12 else [float(v) for v in vals], 'ratio', float(max(vals)/min(vals)) if len(vals)>1 else None)
