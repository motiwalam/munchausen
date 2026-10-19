#import "../template.typ": *

= Elliptic and genus 2 curves <app-curves>

For a fixed exponent $n$, the equation $b(b + x) = x^n + 1$ of @ch-diophantine is the question which integer points lie on the plane curve
$ U^2 = 4 x^n + x^2 + 4, quad U = 2b + x . $
For $n = 3$ this is an elliptic curve, and the question is settled. For $n = 5$ it is a curve of genus 2, and the question is decidable in principle but not decided. This appendix explains the difference. Silverman @silverman2009 is the standard text on elliptic curves. McCallum and Poonen @mccallum-poonen2012 survey the method of Chabauty and Coleman.

== Curves and their genus <sec-app-curves-genus>

A curve $y^2 = f(x)$, with $f$ a polynomial with rational coefficients and no repeated roots, has genus $g = floor((deg f - 1) slash 2)$. Genus 0 curves (degree 1 or 2) have either no rational point or infinitely many, parametrized by rational functions. Genus 1 curves with a rational point are elliptic curves. Curves of genus at least 2 are different in kind.

#theorem(id: "app-curves-faltings", title: "Faltings", status: "cited")[
  A curve of genus at least 2 over $QQ$ has only finitely many rational points.
]

See @faltings1983. The proof does not say how to find the points. For the equation above, $U^2 = 4x^n + x^2 + 4$ has genus $floor((n - 1) slash 2)$, which is at least 2 for $n >= 5$. So for each fixed $n >= 5$ there are only finitely many solutions (Proposition 18.13 of #lib("18.1")). This is the "each $n$ separately" half of the finiteness question; abc would give the uniform half (@app-abc).

== Elliptic curves <sec-app-curves-elliptic>

An elliptic curve over $QQ$ can be written $y^2 = x^3 + a x^2 + c x + d$ with a cubic without repeated roots, together with a point at infinity. Its rational points form an abelian group under the chord and tangent construction: three points add to zero when they lie on a line.

#theorem(id: "app-curves-mordell-weil", title: "Mordell-Weil", status: "cited")[
  The group $E(QQ)$ of rational points of an elliptic curve is finitely generated: $E(QQ) tilde.equiv ZZ^r times T$ with $T$ finite. The number $r$ is the rank.
]

Integral points, with $x$ and $y$ integers, are much rarer than rational points.

#theorem(id: "app-curves-siegel", title: "Siegel", status: "cited")[
  An elliptic curve given by an equation with integer coefficients has only finitely many integral points.
]

Siegel's proof is not effective. Baker's method (@app-baker), applied to elliptic logarithms, makes it effective: given generators of $E(QQ)$, one can bound and then list all integral points. PARI and Sage implement this.

#example(title: [The exponent $n = 3$])[
  For $n = 3$, multiply $U^2 = 4 x^3 + x^2 + 4$ by 16 and put $X = 4x$, $Y = 4U$:
  $ Y^2 = X^3 + X^2 + 64 . $
  This elliptic curve has conductor 433 and rank 2, and exactly 10 integral points (computed with Sage, #lib("16.2", "18.1")). They give the solutions $x = 3, 5, 8, 64, 119$ of $b(b + x) = x^3 + 1$. For instance $x = 3$ gives $U^2 = 108 + 9 + 4 = 121$, $U = 11$ and $b = 4$: the string $(1, 3, 1)$ satisfies $b(b+3) = 3^3 + 1$ in base 4. The point with $x = 119 = 7 dot 17$ is the mixed solution that shows the limits of the method of @sec-dio-baker. The same computation with $x^n + 25$ in place of $x^n + 1$ gives the curve $Y^2 = X^3 + X^2 + 1600$ (#lib("20.4")).
]

The rank is hard to compute in general. Its analytic counterpart is the order of vanishing at $s = 1$ of the $L$-function of the curve, the analytic rank. The conjecture of Birch and Swinnerton-Dyer says that the two ranks agree. It is proven when the analytic rank is 0 or 1, and open otherwise.

== Genus 2 curves and Chabauty's method <sec-app-curves-chabauty>

For a curve $C$ of genus $g >= 2$, the rational points embed into the Jacobian $J$, an abelian variety of dimension $g$ whose rational points again form a finitely generated group $J(QQ) tilde.equiv ZZ^r times T$.

#theorem(id: "app-curves-chabauty", title: "Chabauty, Coleman", status: "cited")[
  If the rank $r$ of $J(QQ)$ is smaller than the genus $g$, then $p$-adic integration on $J$ produces a nonzero function that vanishes on all rational points of $C$. This gives an explicit finite set that contains all of them, and often the exact set.
]

See @chabauty1941 and @coleman1985. The condition $r < g$ is essential: the closure of $J(QQ)$ inside the $p$-adic points of $J$ has dimension at most $r$, and when $r < g$ it meets the curve in finitely many points. A more recent method, quadratic Chabauty, handles some curves with $r = g$. For $r > g$ neither applies.

#example(title: [The exponent $n = 5$])[
  For $n = 5$ the curve is $b^2 + x b = x^5 + 1$, of genus 2, with conductor $800027 = 331 dot 2417$. Its known rational points have $x in {-1, 0, 1, 1 slash 64}$, plus the points at infinity. PARI computes the analytic rank of the Jacobian as 3 (#lib("18.1")). If the rank is 3, it exceeds the genus, so neither Chabauty-Coleman nor quadratic Chabauty applies. What remains is Baker's method for integral points on hyperelliptic curves, combined with the Mordell-Weil sieve (Bugeaud, Mignotte, Siksek, Stoll and Tengely @bmsst2008). It needs a 2-descent on the Jacobian and a basis of $J(QQ)$, which the available software did not provide here. So $n = 5$ is decidable but not decided. A sieve shows that there is no solution with $x <= 10^(10)$.
]

For larger odd $n$ the genus grows, and the same tools apply in principle, one curve at a time. They cannot treat all $n$ at once, and the diagonal $n = x$, the case of Munchausen numbers, is an infinite family of curves of growing genus. This is why @ch-diophantine uses the quadratic field and linear forms in logarithms for the uniform results, and curves only for small $n$.
