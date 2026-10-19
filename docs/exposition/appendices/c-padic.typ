#import "../template.typ": *

= $p$-adic numbers and Hensel lifting <app-padic>

Congruences modulo a prime power $p^e$ appear throughout the main text: in the sieve for short solutions (@sec-search-short), in the local factors of the root heuristic (@sec-short-heuristic), in the residues of $x^x - x$ that make coverings (@sec-short-coverings), and in the $x$-adic form of the equation $b(b + x) = x^x + 1$ (@ch-diophantine). The $p$-adic numbers organize all congruences modulo powers of one prime into a single object. Gouvea's book @gouvea1997 is a friendly introduction.

== Valuations and the $p$-adic integers <sec-app-padic-zp>

#definition(id: "app-padic-def-val", title: [$p$-adic valuation])[
  Fix a prime $p$. For a nonzero integer $n$, the valuation $v_p (n)$ is the exponent of $p$ in $n$, so $n = p^(v_p (n)) m$ with $p divides.not m$. Put $v_p (0) = infinity$, extend to fractions by $v_p (a slash c) = v_p (a) - v_p (c)$, and define the $p$-adic absolute value $|x|_p = p^(-v_p (x))$.
]

A number is $p$-adically small when it is divisible by a high power of $p$. So $3^(10)$ is tiny in the 3-adic sense, and $1 + 3 + 9 + 27 + dots$ converges 3-adically (to $-1 slash 2$, by the geometric series). The absolute value satisfies the strong triangle inequality $|x + y|_p <= max(|x|_p, |y|_p)$.

#definition(id: "app-padic-def-zp", title: [$p$-adic integers])[
  A $p$-adic integer is a sequence $(a_1, a_2, dots)$ with $a_e$ a residue modulo $p^e$ and $a_(e+1) equiv a_e med (mod p^e)$ for every $e$. They form a ring $ZZ_p$ that contains $ZZ$ (an integer $n$ is the sequence of its residues). Equivalently, $ZZ_p$ is the set of formal series $c_0 + c_1 p + c_2 p^2 + dots$ with digits $0 <= c_i < p$, added and multiplied with carries.
]

An element of $ZZ_p$ is a unit exactly when $p$ does not divide its first residue $a_1$. A statement that holds modulo $p^e$ for every $e$ is a statement about $ZZ_p$. This is the language of the "$p$-adic laws" of $x^x - x$ in the library (#lib("20.2")).

== Hensel's lemma <sec-app-padic-hensel>

How do roots modulo $p$ extend to roots modulo $p^2, p^3, dots$? Newton's method answers this, with the $p$-adic absolute value in place of the real one.

#theorem(id: "app-padic-hensel", title: "Hensel's lemma", status: "cited")[
  Let $f$ be a polynomial with coefficients in $ZZ_p$ and let $a$ be an integer with $f(a) equiv 0 med (mod p)$ and $f'(a) equiv.not 0 med (mod p)$. Then for every $e >= 1$ there is exactly one residue $a_e$ modulo $p^e$ with $a_e equiv a med (mod p)$ and $f(a_e) equiv 0 med (mod p^e)$. Together they form the unique root of $f$ in $ZZ_p$ that reduces to $a$.
]

#proof[
  Suppose $f(a_e) equiv 0 med (mod p^e)$. Try $a_(e+1) = a_e + t p^e$. By Taylor expansion, $f(a_e + t p^e) equiv f(a_e) + t p^e f'(a_e) med (mod p^(e+1))$. Since $f'(a_e) equiv f'(a)$ is a unit modulo $p$, there is exactly one $t$ modulo $p$ that makes the right side vanish.
]

A simple root modulo $p$ therefore lifts uniquely. A multiple root, with $f'(a) equiv 0$, can lift to no root or to many.

#example(title: "Multiple roots")[
  $f(r) = r^2 - p$ has the double root $0$ modulo $p$, but no root modulo $p^2$, since $r^2 equiv p$ forces $p | r$ and then $p^2 | r^2$. On the other hand $g(r) = r^2$ has the double root 0 modulo $p$, and modulo $p^2$ it has the $p$ roots $0, p, 2p, dots$. In the root heuristic of @sec-short-heuristic this matters: 3435 = $(3, 4, 3, 5)$ in base 10 has two roots of $Q_s$ modulo 2, but only one modulo 64, so its 2-adic weight halves (#lib("19.3")).
]

== Counting roots modulo $p^e$ <sec-app-padic-count>

Let $N(p^e)$ be the number of roots of a polynomial modulo $p^e$. The root heuristic of @sec-short-heuristic weighs each digit string by such counts. The right local factor at $p$ is $N(p^e)$ for large $e$, not the count modulo $p$ alone, because the event "$p^e$ divides $Q_s (b)$" for a random integer $b$ has probability $N(p^e) slash p^e$, against $p^(-e)$ for a random value. If all roots modulo $p$ are simple, $N(p^e) = N(p)$ for every $e$ by Hensel's lemma.

#proposition(id: "app-padic-average", title: "The average is one", src: "19.3")[
  Fix a polynomial $g$ with integer coefficients and let the constant term vary: $f_c (r) = g(r) - c$. Averaged over the $p^e$ residues $c$ modulo $p^e$, the number of roots of $f_c$ modulo $p^e$ is exactly 1.
]

#proof[
  Each of the $p^e$ residues $r$ is a root of $f_c$ for exactly one $c$, namely $c = g(r)$. So the total number of roots over all $c$ is $p^e$.
]

For a Munchausen polynomial the constant term $s_k - F(s)$ is the part that the weights $x^x$ control, and in the model it behaves like a random residue. So the local factors are unbiased: they average to 1 and only redistribute the weight among strings. This is why the completeness estimates of @sec-short-heuristic do not depend on which version of the factor one uses.

== The exponential and the logarithm <sec-app-padic-exp>

The $p$-adic exponential and logarithm are defined by the usual series,
$ exp(z) = sum_(n >= 0) z^n / n!, quad log(1 + z) = sum_(n >= 1) (-1)^(n+1) z^n / n . $
The logarithm converges for $|z|_p < 1$, that is for $z in p ZZ_p$. The exponential converges only for smaller $z$, because $n!$ is divisible by a high power of $p$: one needs $v_p (z) > 1 slash (p - 1)$. For odd $p$ that means $z in p ZZ_p$, and for $p = 2$ it means $z in 4 ZZ_2$.

#theorem(id: "app-padic-explog", title: "Exp and log", status: "cited")[
  For odd $p$, $exp$ and $log$ are inverse bijections between $p ZZ_p$ and $1 + p ZZ_p$, and they turn sums into products. For $y in 1 + p ZZ_p$ and an integer $x$, $y^x = exp(x log y)$.
]

See @gouvea1997[section 4.5]. With this, a power $x^x$ with $x$ in a fixed residue class becomes a power series in a $p$-adic variable. The library uses it to find the exact set $T(p^e)$ of residues of $x^x - x$ modulo $p^e$ (#lib("20.2")).

== The 3-adic law of $x^x - x$ <sec-app-padic-three>

The covering theorem @thm-covering rests on one congruence. Here is its elementary proof, as a model for the $p$-adic arguments of @sec-short-coverings.

#proposition(id: "app-padic-mod27", title: "Residues modulo 27", src: "15.4")[
  For every integer $x >= 1$: if $x equiv 2 med (mod 6)$ then $x^x - x equiv 2 med (mod 27)$; otherwise $x^x - x equiv 0 med (mod 3)$.
]

#proof[
  If $3 | x$, both terms vanish modulo 3. If $x equiv 1 med (mod 3)$, then $x^x equiv 1 equiv x$. If $x equiv 5 med (mod 6)$, then $x$ is odd and $x equiv -1 med (mod 3)$, so $x^x equiv (-1)^x = -1 equiv x$.

  Now let $x equiv 2 med (mod 6)$. Then $x$ is even and $3 | x + 1$. Put $u = -x = 1 + 3t$ with $3t = -(x + 1)$. Since $x$ is even, $x^x = u^x$. By the binomial theorem,
  $ u^x = sum_j binom(x, j) (3t)^j equiv 1 + x (3t) + binom(x, 2) (3t)^2 med (mod 27), $
  because $(3t)^j$ is divisible by 27 for $j >= 3$. Substituting $3t = -(x + 1)$ and simplifying gives
  $ x^x - x equiv 2 + ((x + 1)^3 (x - 2)) / 2 med (mod 27), $
  and $27 | (x + 1)^3$.
]

So modulo 27 the values of $x^x - x$ prime to 3 are all equal to 2. The full law (Theorem 20.11 of #lib("20.2")) uses the exponential: on the class $x equiv 2 med (mod 6)$ one writes $x = -exp(3w)$ and expands $x^x - x$ as $2 + 27 G(w)$ with a power series $G$. Modulo 3, $G(w) equiv -(w^3 + w^4)$, which never takes the value 2. Hensel's lemma applied to $G$ then gives the exact set for every power of 3: the multiples of 3, together with the residues $equiv 2 med (mod 27)$ that are not $equiv 56 med (mod 81)$. Beyond 81 a single power of 3 adds no new constraint. For primes $p >= 7$, every residue modulo $p^e$ is a value of $x^x - x$, so those primes alone can never cover a family (Theorem 20.8).
