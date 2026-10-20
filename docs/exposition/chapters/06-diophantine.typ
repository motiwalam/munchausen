#import "../template.typ": *

= The equation $b(b + x) = x^n + c$ <ch-diophantine>

The 3-digit solution $(1, 7, 1)$ in base 904 looks like a pure coincidence.
This chapter shows that it is not quite one. It belongs to a family of
strings whose solutions are the solutions of a single exponential
Diophantine equation, and that equation can be attacked with the tools of
algebraic number theory: cyclotomic and Aurifeuillian factors, units and
ideal classes of quadratic fields, and lower bounds for linear forms in
logarithms. The family is far from solved, but the attack shows exactly
where the difficulty lies. The appendices on quadratic fields
(@app-quadratic), linear forms in logarithms (@app-baker), the abc
conjecture (@app-abc) and curves (@app-curves) give the background.

== Where the equation comes from <sec-dio-setting>

Take the 3-digit string $(1, x, r)$ in base $b$. Its value is
$b^2 + x b + r$ and its weight is $1 + x^x + w(r)$. So it is a solution
exactly when
$
  b (b + x) = x^x + c, quad quad c = w(r) - r + 1.
$
For $r = 1$ under either convention, and for $r = 0$ under $0^0 = 0$, the
constant is $c = 1$. The digits $r = 2$ and $r = 3$ give $c = 3$ and
$c = 25$. The question becomes: for which $x$ does $x^x + c$ factor as
$b (b + x)$, a product of two numbers that differ by exactly $x$? It is
natural to replace the exponent $x$ by a free exponent $n$:
$
  b (b + x) = x^n + c.
$ <eq-dio-main>
Completing the square, with $U = 2b + x$, turns it into
$U^2 = 4 x^n + x^2 + 4c$: a question about squares in a sequence that grows
exponentially. For $n = 1$ and $c = 1$, $b = 1$ is a solution for every $x$.

#computation(id: "dio-known", title: [Known solutions for $c = 1$, $n = x$], src: ("3.2", "16.2"))[
  The equation $b(b + x) = x^x + 1$ has the solutions $x = 3$, $b = 4$ and
  $x = 7$, $b = 904$, and no other with $x <= 4 dot 10^9$. They give
  $(1, 3, 1)$ in base 4 and $(1, 7, 1)$ in base 904 under $0^0 = 1$, and
  also $(1, 3, 0)$ and $(1, 7, 0)$ under $0^0 = 0$.
]

Every 3-digit solution $(p, q, r)$ in base $b$ gives a factorization
$F - r = b(p b + q)$. Most of them come from an algebraic identity,
completed by one small coincidence between powers (@tab-dio-pairs).

#tablefig(caption: [The factor pair $F - r = b (p b + q)$ of each 3-digit
  solution #lib("16.1").], id: "tab-dio-pairs")[
  #btable(
    columns: 4,
    align: (left, left, left, left),
    [solution], [$F - r$], [pair $(b, p b + q)$], [identity],
    [$(1,3,1)$, base 4], [$3^3 + 1 = 28$], [$(4, 7)$], [cyclotomic and Aurifeuillian],
    [$(1,7,1)$, base 904], [$7^7 + 1$], [$(8 dot 113, 911)$], [Aurifeuillian (@sec-dio-aurifeuille)],
    [$(1,2,6)$, base 215], [$6^6 - 1$], [$(6^3 - 1, 6^3 + 1)$], [difference of squares; needs $2^2 + 1 - 6 = -1$],
    [$(5,1,3)$, base 25], [$5^5 + 5^2$], [$(5^2, 5^3 + 1)$], [square class; needs $3^3 - 3 + 1 = 5^2$],
    [$(3,1,3)$, base 4], [$2(3^3 - 1) = 52$], [$(4, 13)$], [$4 = 2 Phi_1 (3)$, $13 = Phi_3 (3)$],
    [$(6,1,5)$, base 91], [$7 dot 13 dot 547$], [$(91, 547)$], [none],
  )
]

Only $(6, 1, 5)$ in base 91 has no algebraic factor pair: it needs
$6 dot 5^5 equiv 4 med (mod 91)$, a coincidence. The 4-digit solutions show
no such structure. For 3435, $F - r = 3430 = 10 dot 7^3$ is a cube times 10
by chance.

== Aurifeuillian factors and base 904 <sec-dio-aurifeuille>

For odd $x$, $x^x + 1$ is the product of the cyclotomic values
$Phi_(2d)(x)$ over the divisors $d$ of $x$ (@app-quadratic). The two
factors $b$ and $b + x$ of a solution are coprime: a common prime divides
$x$ and $x^x + 1$, but $x^x + 1 equiv 1 med (mod x)$.

#proposition(id: "dio-prime-x", title: [The factor form for prime $x$], src: "16.1")[
  Let $x$ be an odd prime and $Phi = Phi_(2x)(x)$, so that
  $x^x + 1 = (x + 1) Phi$. Every solution of $b(b + x) = x^x + 1$ has
  $b = (x + 1) A$, $b + x = B$ or $b = A$, $b + x = (x + 1) B$, with
  $A B = Phi$ and $A equiv B equiv 1 med (mod 2x)$.
]
#proof[
  A prime $p | Phi$ has $x^x equiv -1 med (mod p)$, so $x$ has order $2x$
  modulo $p$ and $p equiv 1 med (mod 2x)$. So every divisor of $Phi$ is
  $1 med (mod 2x)$. Write $b = d A$, $b + x = e B$ with $d e = x + 1$,
  $gcd(d, e) = 1$ and $A B = Phi$. Reducing $e B - d A = x$ modulo $x$
  gives $e equiv d med (mod x)$. Since $|e - d| < x + 1$, either $e = d$,
  impossible for coprime $d, e$ with $d e > 1$, or $|e - d| = x$, which
  forces $\{d, e\} = \{1, x + 1\}$.
]

For $x = 7$ the pair is $A = 113$, $B = 911$, and $904 = 8 dot 113$. For
$x = 3$ it is $A = 1$, $B = 7$. Both use the _Aurifeuillian_ factorization
of $Phi_(2x)(x)$. For squarefree $x equiv 3 med (mod 4)$, the polynomial
$Phi_(2x)(x t^2)$ splits in $ZZ[t]$ into two factors of degree $phi(x)$.
Their values at $t = 1$ are two integers $L < M$ with $L M = Phi_(2x)(x)$.
For $x = 7$, $Phi_(14)(7) = 113 dot 911$. The same holds for squarefree
$x equiv 1 med (mod 4)$ with $Phi_x (x t^2)$, a factor of $x^x - 1$.

=== The ratio of the two factors

For $x$ from 7 to 79 the ratio $M slash L$ stays between 6.98 and 8.06,
near $e^2 = 7.389$. This is a theorem.

#theorem(id: "thm-aurifeuille", title: "The ratio of Aurifeuillian factors", src: "16.1")[
  For squarefree odd $x > 1$, the Aurifeuillian factors $L < M$ of
  $x^x plus.minus 1$ satisfy
  $
    ln (M / L) = 2 sum_(j "odd", thin gcd(j, x) = 1) psi(j) / (j x^((j-1) slash 2)),
  $
  with $psi$ the quadratic character of $QQ(sqrt(x))$. So
  $ln(M slash L) = 2 + (2 slash 3)(x slash 3) slash x + O(x^(-2))$ when
  $3 divides.not x$, where $(x slash 3)$ is the Legendre symbol, and always
  $|ln(M slash L) - 2| <= 2 slash (3(x - 1))$. In particular $M slash L -> e^2$.
]
#sketch[
  Take $x equiv 3 med (mod 4)$ and a primitive $4x$-th root of unity
  $zeta$. The roots of $Phi_(2x)(x t^2)$ are $zeta^a slash sqrt(x)$ for $a$
  prime to $4x$. The set $A = {a : psi(a) = 1}$ is stable under the Galois
  group, so $L$ and $M$ are, up to order, $|G(1)|$ and $|G(-1)|$ with
  $G(t) = x^(phi(x) slash 2) product_(a in A) (t - zeta^a slash sqrt(x))$.
  Expanding $ln |1 plus.minus zeta^a slash sqrt(x)|$ in powers of
  $1 slash sqrt(x)$ gives
  $ln(M slash L) = 2 op("Re") sum_(j "odd") S_j slash (j x^(j slash 2))$
  with $S_j = sum_(a in A) zeta^(a j)$. Half of $S_j$ is a Ramanujan sum,
  which vanishes for odd $j$, and the other half is a Gauss sum
  $psi(j) tau(psi)$ with $tau(psi) = 2 sqrt(x)$. So $S_j = psi(j) sqrt(x)$.
]

The values agree with the series to within $10^(-30)$ for all 132 squarefree
odd $x$ up to 300 #lib("16.1"). The term $x (ln (M slash L) - 2)$ tends to
$plus.minus 2 slash 3$ with the sign of $(x slash 3)$, and to 0 when
$3 | x$. For $x = 7$ it is $+0.610$, so $M slash L = 8.0619$.

=== Why $x = 7$ works and nothing larger does

#proposition(id: "dio-mod-x2", title: [The pair is a solution modulo $x^2$], src: "16.1")[
  For a prime $x equiv 3 med (mod 4)$,
  $L equiv 1 - x + x (x - 1) slash 2$ and
  $M equiv 1 + x + x (x - 1) slash 2 med (mod x^2)$. So
  $E = M - (x + 1) L - x$ is divisible by $x^2$, and the pair
  $b = (x + 1) L$, $b + x = M$ satisfies $b(b + x) equiv x^x + 1$ modulo
  $x^2$.
]

The proof expands $L$ and $M$ in powers of $sqrt(x)$; the coefficients are
the elementary symmetric functions of the roots of unity in the set $A$ of
@thm-aurifeuille.#footnote[The library states the congruences for $L$ and
$M$ for squarefree $x equiv 3 med (mod 4)$, with $(x + mu(x)) slash 2$ in
place of $(x - 1) slash 2$. Only prime $x$ matters here: for composite $x$
the product $(x + 1) L M$ is not $x^x + 1$, because $x^x + 1$ has further
cyclotomic factors.]
So for every prime $x equiv 3 med (mod 4)$ the Aurifeuillian pair solves the
equation to precision $x^2$. A
true solution needs $E = 0$. By @thm-aurifeuille,
$M - (x + 1) L = L (M slash L - x - 1)$, and $M slash L < 8.1 < x + 1$ for
$x >= 11$, so $E < 0$. For $x = 7$, $M slash L = 8.06$ lies within $x slash L$
of $x + 1 = 8$, and $E = 0$. For $x = 3$, $L = 1$ and $E = 0$. So
$(1, 7, 1)$ in base 904 is Aurifeuillian in a precise sense: the identity
gives the factor pair and the congruence modulo $x^2$, and what remains is
the numerical coincidence $M slash L = e^(2 + 0.61 slash 7) approx 8.06$,
close to $x + 1 = 8$.

#theorem(id: "dio-no-algebraic", title: "No other algebraic factor pair", src: "16.1")[
  Let $x >= 3$ be odd. If $b(b + x) = x^x + 1$ and $b$ is a product of
  algebraic factors of $x^x + 1$, that is of cyclotomic values and
  Aurifeuillian halves, then $x = 3$ or $x = 7$.
]
#sketch[
  A solution has $|ln((x^x + 1) slash b^2)| = ln(1 + x slash b)$, which is
  below $x^(2 - x slash 2)$. On the other side, $ln Phi_(2d)(x)$ is
  $phi(d) ln x$ up to $1 slash (x - 1)$, and each Aurifeuillian pair splits
  its logarithm into halves that differ by $ln(M_d slash L_d)$. The
  difference $ln((x^x + 1) slash b) - ln b$ is then an odd multiple $D$ of
  $ln x$, plus small errors, plus a sum of the ratios $ln(M_d slash L_d)$.
  By @thm-aurifeuille each ratio is near 2 or small, and a case analysis
  shows that the total cannot be near 0 unless $x in {3, 7}$.
]

A computation over all odd $x$ up to 201 confirms this: the best algebraic
split has $|ln(x^x + 1) - 2 ln b|$ equal to 0.0077 for $x = 7$ and at least
0.54 for every $x >= 11$ #lib("16.1"). A separate exhaustive search of
3-digit strings with two digits up to 1000 and the third up to 30 finds no
new 3-digit solution, in bases up to about $10^(1500)$.

=== The general series

The series of @thm-aurifeuille is one case of a general law. Let $s > 1$
be squarefree, $D$ the discriminant of $QQ(sqrt(s))$, $chi$ its Kronecker
symbol, $k >= 1$ odd, and $m = k |D| slash 2$ for even $D$, $m = k |D|$ for
odd $D$. Then $Phi_m (s t^2)$ splits into two Aurifeuillian factors, whose
values at $t = y$ are $L <= M$. Define the twisted Ramanujan sum
$g_k (j) = sum_(r | gcd(j, k)) r mu(k slash r) chi(k slash r) chi(j slash r)$.

#theorem(id: "dio-general-series", title: "The ratio in general", src: "18.5")[
  For $s y^2 > 1$,
  $
    ln (M / L) = 2 lr(| sum_(j "odd") (g_k (j)) / (j s^((j-1) slash 2) y^j) |).
  $
  Since $g_k (1) = mu(k) chi(k)$, $M slash L -> e^(2 slash y)$ as $s$ grows
  when $k$ is squarefree and prime to $D$, and $M slash L -> 1$ otherwise.
]

The proof for even $D$ is the Gauss-sum computation above, with the
standard formula for Gauss sums of induced characters. The odd case follows
by the same computation with the character $chi(a)(-1)^a$ on the exponents.
Both cases were checked numerically: in 456 cases ($s <= 40$, odd $k <= 15$, $y <= 4$) the
series agrees with the factored polynomial to within $2 dot 10^(-62)$
#lib("18.5"). For the equation this says that an Aurifeuillian pair with
$y >= 2$ is balanced within a factor $e^(1 + o(1))$, so the $e^2$
coincidence of $x = 7$ needs $y = 1$.

== Elementary exclusions and the limits of congruences <sec-dio-elementary>

From now on write the equation as $U^2 = 4 x^n + x^2 + 4$ with
$U = 2 b + x$, for $c = 1$.

#proposition(id: "dio-elementary", title: "Elementary exclusions", src: ("16.2", "18.1"))[
  The equation $b(b + x) = x^n + 1$ has no solution in each of these cases:
  (a) $n >= 4$ even; (b) $n >= 4$ and $x$ a square; (c) $n >= 2$ and
  $x equiv 2 med (mod 4)$; (d) $n >= 2$ and $x equiv 4 med (mod 8)$. For
  $n = x$ this excludes every even $x$ and every odd square.
]
#proof[
  (a), (b): then $x^n = Y^2$ for an integer $Y = x^(n slash 2)$, and
  $(2Y)^2 < U^2 < (2Y + 1)^2$ because $0 < x^2 + 4 < 4Y + 1$. (c), (d): $x$
  is even, so $U = 2V$ and $V^2 = x^n + (x slash 2)^2 + 1$. This is
  $2 med (mod 4)$ if $x equiv 2 med (mod 4)$ and $5 med (mod 8)$ if
  $x equiv 4 med (mod 8)$. Neither is a square.
]

For odd $x$, $4 x^x + x^2 + 4 equiv 1 med (mod 8)$ and it is
$4 med (mod p)$ for every prime $p | x$, so it is a square at 2 and at the
primes of $x$. Could congruences at other primes finish the proof? A sieve
gets very far.

#computation(id: "dio-sieve", title: [The sieve to $4 dot 10^9$], src: "16.2")[
  For every $x$ from 2 to $4 dot 10^9$ other than 3 and 7, some odd prime
  $p <= 229$ makes $4 x^x + x^2 + 4$ a quadratic non-residue modulo $p$. So
  $b(b + x) = x^x + 1$ has no further solution with $x <= 4 dot 10^9$, that
  is with $b$ up to about $10^(1.9 dot 10^(10))$. The 31 primes $p$ with
  $p - 1 | 20160$ exclude all but a density $1.5 dot 10^(-4)$ of all
  integers $x$.
]

But no finite set of primes can finish the job.

#proposition(id: "dio-no-congruence", title: "Congruences cannot finish the proof", src: "16.2")[
  For every finite set $S$ of primes, the integers
  $x equiv 1 med (mod op("lcm")(p - 1 : p in S))$ pass the test at every
  $p in S$. They have positive density.
]
#proof[
  If $x equiv 1 med (mod p - 1)$ and $p divides.not x$, then
  $x^x equiv x med (mod p)$ by Fermat, so
  $4 x^x + x^2 + 4 equiv (x + 2)^2$ is a square. If $p | x$, the value is
  $4$, also a square.
]

The reason is the trivial solution $b = 1$ of the equation with $n = 1$.
At the primes where $x equiv 1 med (mod p - 1)$, the power $x^x$ looks like
$x^1$. Any proof must use infinitely many primes, or global information.

One more reformulation shows how thin the target is.

#proposition(id: "dio-xadic", title: [The $x$-adic form], src: "16.2")[
  Let $x$ be an odd prime and $beta$ the root of $t^2 + x t - 1 = 0$ in the
  $x$-adic integers $ZZ_x$ with $beta equiv 1 med (mod x)$. Let $R$ be the
  residue of $beta$ modulo $x^x$ in $[0, x^x)$. Then
  $b(b + x) = x^x + 1$ has a solution exactly when $R < x^(x slash 2)$,
  and then $b = R$.
]
#proof[
  A solution has $b equiv 1 med (mod x)$ by @dio-prime-x, and $b$ is a root
  of $t^2 + x t - 1$ modulo $x^x$. Hensel's lemma (@app-padic) gives a
  unique such root that is $1$ modulo $x$, so $b equiv beta$, and
  $b < x^(x slash 2)$. Conversely, if $R < x^(x slash 2)$, then
  $R(R + x) - 1$ is a positive multiple of $x^x$ below $2 x^x$, so it equals
  $x^x$.
]

So a solution means that the top $(x - 1) slash 2$ base-$x$ digits of the
$x$-adic number $beta$, cut off at $x^x$, all vanish. For $x = 7$,
$R = 904$ and $7^(3.5) = 907.5$. For the other primes up to 59, $R$ lies
between $x^(x - 0.8)$ and $x^x$, as for a random residue. Heuristically the
chance is $x^(-x slash 2)$. Statements that a block of consecutive digits of
an algebraic $p$-adic number vanishes are open even for one fixed base.

== The quadratic field <sec-dio-field>

The equation is a norm equation in a real quadratic field (@app-quadratic).
Let $x$ be odd, $D = x^2 + 4$, $K = QQ(sqrt(D))$, and
$
  epsilon = (x + sqrt(D)) / 2, quad quad epsilon' = (x - sqrt(D)) / 2 = -1 / epsilon.
$
Then $epsilon$ is a unit of norm $-1$ and trace $x$, and for every integer
$b$
$
  N(b + epsilon) = (b + epsilon)(b + epsilon') = b^2 + b x - 1.
$
So the equation $b(b + x) = x^n + 1$ says exactly $N(b + epsilon) = x^n$.

#lemma(id: "dio-splitting", title: "Splitting", src: "18.1")[
  Let $x$ be odd and $b$ a solution.
  + The ideals $(b + epsilon)$ and $(b + epsilon')$ are coprime.
  + Every prime $p | x$ splits in $K$.
  + $P = (epsilon + 1)$ has norm $x$, its conjugate is
    $P' = (epsilon' + 1)$, $P P' = (x)$, and $P$, $P'$ are coprime.
]
#proof[
  (1) A common prime ideal divides the difference $sqrt(D)$ and the product
  $x^n$, but $gcd(D, x) = 1$. (2) $D equiv 4 med (mod p)$ is a nonzero
  square. (3) $N(epsilon + 1) = epsilon epsilon' + epsilon + epsilon' + 1 = x$,
  and the difference of $epsilon + 1$ and $epsilon' + 1$ is $sqrt(D)$,
  prime to $x$.
]

#lemma(id: "dio-power", title: [The ideal is an $n$-th power], src: "18.1")[
  For a solution with $x$ odd, $(b + epsilon) = B^n$, where $B$ is the
  product over the prime powers $p^a$ exactly dividing $x$ of $q_p^a$, with
  $q_p$ one of the two primes above $p$. Moreover $B != B'$.
]

#proof[
  $(b + epsilon)(b + epsilon') = (x)^n$ is the product of the ideals
  $(pi_p pi'_p)^(a n)$ over the primes $p | x$, where $pi_p$ and $pi'_p$ are
  the two primes above $p$. By @dio-splitting each $pi_p^(a n)$ divides
  exactly one of the two coprime factors, and its conjugate divides the
  other. Collecting the factors of $(b + epsilon)$ gives $B^n$. If $B = B'$,
  then $B$ would contain both $pi_p$ and $pi'_p$ for some $p$, and both
  factors would share a prime.
]

Call a solution _pure_ if $B = P$ or $B = P'$, and _mixed_ otherwise. If $x$
is a prime power, every solution is pure. A pure solution gives an explicit
element: $b + epsilon = u (epsilon + 1)^n$ for a unit $u$.

#proposition(id: "dio-unit-form", title: "The unit form", src: "16.2")[
  Let $x equiv 3 med (mod 4)$ be squarefree with $x^2 + 4$ prime, and let
  $eta$ be the fundamental unit of $ZZ[sqrt(x)]$. A solution of
  $b(b + x) = x^x + 1$ gives
  $(2b + x) + 2 x^((x-1) slash 2) sqrt(x) = plus.minus (x + 2 plus.minus 2 sqrt(x)) eta^k$
  for some integer $k$.
]
#proof[
  Both sides have norm $x^2 + 4 = p$, a prime that splits in $QQ(sqrt(x))$.
  The two elements $x + 2 plus.minus 2 sqrt(x)$ generate the two primes above
  $p$, so the left side is one of them times a unit of norm 1.
]

For $x = 3$ and $x = 7$, with $k = 2$ in both cases:
$
  11 + 6 sqrt(3) = (5 - 2 sqrt(3))(2 + sqrt(3))^2, quad quad
  1815 + 686 sqrt(7) = (9 + 2 sqrt(7))(8 + 3 sqrt(7))^2.
$
So the equation asks whether one coordinate of a binary recurrence is ever
$2 x^((x-1) slash 2)$. For fixed $x$ that is a classical finiteness problem
@shorey-tijdeman1986. The difficulty is that the field changes with $x$.

=== A lower bound for the exponent

Let $eta_0 > 1$ be the fundamental unit of $K$ and $mu_0 = ln eta_0$.
Since $N(epsilon) = -1$, $epsilon = eta_0^r$ with $r$ odd, and
$mu_0 >= op("arcsinh")(1 slash 2) = 0.4812$. Put
$Lambda_0 = ln((b + epsilon) slash (b + epsilon'))$. Since
$b > x^(n slash 2) - x slash 2$,
$
  0 < Lambda_0 < tau_n = sqrt(D) / (x^(n slash 2) - x slash 2 - 1),
$ <eq-dio-tau>
which is tiny: for $x >= 3$ and $n >= 5$, $tau_n < 0.276$. Let
$z = (epsilon + 1) slash (epsilon - 1)$. Then $ln z = 2 op("artanh")(1 slash epsilon) < 2.2 slash x$
for $x >= 3$, and the exact series
$x ln z = 2 - sum_(i >= 1) 4 epsilon^(-2i) slash ((2i - 1)(2i + 1))$ shows
that $x ln z$ lies just below 2.

#proposition(id: "dio-pure-lower", title: "Pure solutions need a large exponent", src: "18.1")[
  Let $x$ be odd, $n >= 5$ odd, and $b$ a pure solution. Then there is an
  odd integer $s >= 1$ with $|n ln z - s mu_0| = Lambda_0 < tau_n$. In
  particular $n ln z >= mu_0 - tau_n$, and $x < 11 n$.
]
#proof[
  Suppose $B = P$. Then $b + epsilon = u (epsilon + 1)^n$ with
  $u = plus.minus eta_0^k$, and $b + epsilon' = u' (epsilon' + 1)^n$. The
  quotient of $epsilon + 1$ by $epsilon' + 1$ is $epsilon z$, and
  $|u slash u'| = eta_0^(2k)$. Taking logarithms gives
  $Lambda_0 = 2 k mu_0 + n (r mu_0 + ln z) = n ln z - s mu_0$ with
  $s = -(2k + n r)$ odd. The case $B = P'$ is the same with the roles
  exchanged. If $s <= -1$, the left side would be at least
  $mu_0 > tau_n$, against @eq-dio-tau. Finally
  $n >= (mu_0 - tau_n) slash ln z > (0.4812 - 0.276) x slash 2.2 > 0.093 x$.
]

For the diagonal $n = x$ this is already decisive, without any deep
theorem.

#proposition(id: "dio-diagonal-pure", title: "The diagonal has no pure solution beyond 7", src: "18.1")[
  For odd $x >= 9$, $b(b + x) = x^x + 1$ has no pure solution. So for odd
  prime powers $x$ the only solutions are $x = 3$ and $x = 7$.
]
#proof[
  With $n = x$, $tau_x < 5 dot 10^(-4)$ and $x ln z$ is within $0.017$ of 2.
  So $|2 - s mu_0| < 0.018$ with $s >= 1$ odd and
  $mu_0 = op("arcsinh")(y slash 2)$ for a positive integer $y$. For $s = 1$
  this needs $y in (7.12, 7.39)$; for $s = 3$, $y in (1.42, 1.45)$; for
  $s >= 5$, $mu_0 < 0.41$, which is impossible. No integer qualifies. The
  value $y = 7$, $s = 1$ is the solution $x = 7$, where $tau_7 = 0.008$ is
  not small. $x = 5$ fails by a direct check.
]

Here is the $e^2$ of @thm-aurifeuille seen from the unit side: $n = x$
forces $s mu_0$ close to 2, and $mu_0 = ln epsilon$ is about $ln x$, which
equals 2 near $x = e^2 = 7.39$.

== Linear forms in logarithms <sec-dio-baker>

For general $n$ the relation $|n ln z - s mu_0| < tau_n$ says that a linear
form in two logarithms is exponentially small. Baker's theory gives lower
bounds for such forms, and comparing the two bounds bounds $n$
(@app-baker).

#theorem(id: "dio-laurent", title: "Laurent", status: "cited", src: "18.1")[
  Let $alpha_1, alpha_2 > 1$ be multiplicatively independent real algebraic
  numbers, $b_1, b_2$ positive integers,
  $Lambda = b_2 ln alpha_2 - b_1 ln alpha_1$,
  $D_g = [QQ(alpha_1, alpha_2) : QQ]$,
  $ln A_i >= max(h(alpha_i), ln(alpha_i) slash D_g, 1 slash D_g)$ with $h$
  the absolute logarithmic height, and
  $b' = b_1 slash (D_g ln A_2) + b_2 slash (D_g ln A_1)$. Then
  $
    ln |Lambda| >= -25.2 D_g^4 max(ln b' + 0.38, 10 slash D_g, 1)^2 ln A_1 ln A_2.
  $
]

This is Corollary 2 of Laurent @laurent2008 with $(m, C_2) = (10, 25.2)$,
the constant for real positive logarithms. The original paper was not
available; the statement and the table of constants agree in two
independent recent sources #lib("18.1", "38.4").

#theorem(id: "dio-pure-all", title: "All pure solutions", src: "18.1")[
  For odd $x$, the only pure solution of $b(b + x) = x^n + 1$ with $n >= 4$
  is $(x, n) = (7, 7)$.
]
#sketch[
  Apply @dio-laurent to $alpha_1 = eta_0$ and $alpha_2 = z$, which are
  independent because $z$ is not an algebraic integer: it is a root of
  $x T^2 - 4 T - x$. For $x >= 10^5$, the lower bound for $Lambda_0$
  against @eq-dio-tau gives $n < 22 thin 000 max(mu_0, 1)$, while
  @dio-pure-lower gives $n > 0.49 x mu_0$ roughly. Together they force
  $x < 10^5$, a contradiction. For odd $x < 10^5$ a computation finds $r$
  and $mu_0$ exactly, bounds $n$ by Laurent's theorem, checks $n <= 15$
  directly, and for larger $n$ uses that $s slash n$ must be a convergent of
  $ln z slash mu_0$ (Legendre's theorem, @app-baker). The only hit is
  $(7, 7)$.
]

#theorem(id: "thm-prime-powers", title: "Prime powers", src: "18.1")[
  Let $x$ be a prime power. The solutions of $b(b + x) = x^n + 1$ with
  $n >= 2$ are exactly $(x, n) = (3, 2), (8, 2), (3, 3), (5, 3), (8, 3), (64, 3), (7, 7)$.
]
#sketch[
  Even $n >= 4$ is excluded by @dio-elementary.
  For $n = 2$ the solutions are the even-index Fibonacci numbers
  $x = F_(2k) = F_k L_k$; a prime power among them needs $F_k$ and $L_k$ to
  be powers of 2, which leaves $x = 3$ and $x = 8$.
  For $n = 3$ the list is complete by the elliptic curve of
  @sec-dio-exponents; $119 = 7 dot 17$ is not a prime power.
  For odd $n >= 5$ and odd $x$ every solution is pure, and
  @dio-pure-all applies.
  For $x = 2^a$, @dio-elementary forces $a >= 3$, and with $V = U slash 2$
  the equation reads $V^2 = 2^(a n) + 2^(2a - 2) + 1$. By Szalay's theorem
  on $2^A + 2^B + 1 = V^2$ @szalay2000 @scott2006, the solutions with
  $A >= B >= 1$ are $(2t, t + 1)$, $(5, 4)$ and $(9, 4)$, and none of them
  has $n >= 5$.
]

In the language of generalized Ramanujan-Nagell equations
$U^2 - D = 4 p^n$ @le-soydan2020, this gives the exact solution set for
$D = p^2 + 4$ and every prime $p$: $n = 1$ always, $n = 2, 3$ for $p = 3$,
$n = 3$ for $p = 5$, and $n = 7$ for $p = 7$.

=== Mixed solutions

A mixed solution has no explicit generator for $B$. Let $d$ be the order of
the class of $B$ in the class group of $K$, so $d | n$. Then $B^d = (eta)$
is principal, and the same argument with $theta = ln |eta slash eta'|$ in
place of $ln z$ gives a linear form in $mu_0$ and $theta$.

#theorem(id: "dio-mixed", title: "Mixed solutions", src: "18.1")[
  Let $x$ be odd and not a square, $n >= 5$ odd, $b$ a solution, and $d$
  the order of the class of $B$. If $d < n$, then $n < 6.4 dot 10^4 d ln x$.
]

#sketch[
  Write $B^d = (eta)$. Then $b + epsilon = u eta^(n slash d)$ with
  $u = plus.minus eta_0^k$, and
  $Lambda_0 = 2 k mu_0 + (n slash d) theta$ with
  $theta = ln |eta slash eta'|$, reduced to $|theta| <= mu_0$. The number
  $w = |eta slash eta'|$ is a root of $x^d T^2 - op("Tr")(eta^2) T + x^d$,
  so its height is at most $(d ln x + |theta|) slash 2$, and $w != 1$
  because $B != B'$. This gives $|theta| >= 0.99 x^(-d slash 2)$, which
  forces $k theta < 0$, and then $Lambda_0$ is a linear form in the two
  logarithms $mu_0$ and $|theta|$. Laurent's theorem against
  @eq-dio-tau gives an inequality whose worst case, over a grid of $x$ from
  3 to $10^(40)$ and $d$ up to 101, is $n slash (d ln x) <= 63 thin 441$.
]

There is no matching lower bound for $n$ here, and the $n = 3$ solution
$x = 119 = 7 dot 17$ shows that mixed solutions exist: its ideal $B$ is not
principal, and its class has order $d = 3 = n$.

#corollary(id: "cor-x-x", title: [The diagonal $n = x$], src: ("18.1", "16.2"))[
  If $b(b + x) = x^x + 1$ has a solution with $x$ other than 3 and 7, then
  $x > 4 dot 10^9$ is odd, composite, not a square and not a prime power,
  the solution is mixed, the ideal $B$ is not principal, and the order $d$
  of its class divides $x$ with $x slash d < 3.3 dot 10^4 ln x$. In
  particular the class number of $QQ(sqrt(x^2 + 4))$ is at least
  $x slash (3.3 dot 10^4 ln x)$.
]
#proof[
  Even $x$ and squares: @dio-elementary. $x <= 4 dot 10^9$: @dio-sieve.
  Prime powers: @thm-prime-powers. Pure solutions: @dio-diagonal-pure.
  Principal $B$: the inequality behind @dio-mixed, evaluated with $d = 1$
  by the script `r2nt_principal.py`, allows only $x <= 747 thin 069$.
  Otherwise $3 <= d$ divides $x$. The same computation shows that for
  $x >= 4 dot 10^9$ and $d >= 3$ the inequality gives
  $n slash (d ln x) < 32 thin 500$; with $n = x$ this is the bound on
  $x slash d$.
]

So under $0^0 = 1$, the string $(1, x, 1)$ is a solution for no odd prime
power $x$ other than 3 and 7, and any further $x$ must be composite, above
$4 dot 10^9$, with a large non-principal ideal class.

For a fixed $x$ the whole argument is a finite procedure.

#computation(id: "dio-small-x", title: [All exponents for odd $x <= 1001$], src: "18.1")[
  For odd $x <= 1001$ the only solution of $b(b + x) = x^n + 1$ with
  $n >= 4$ is $(7, 7)$. The computation builds $K$ with a certified class
  group, runs over all $2^(omega(x))$ ideals $B$ (814 of the 1,818 are not
  principal), and tests the convergents of $theta slash (2 mu_0)$ up to the
  bound of Laurent's theorem, which allows exponents up to 7,816,158.
  With the threshold lowered to $n >= 3$ it finds $(5, 3)$, $(7, 7)$ and
  $(119, 3)$.
]

=== How often the loophole is open

@cor-x-x leaves one loophole: a mixed ideal whose class order $d$ divides
$x$ and is large. Does that happen at all?

#computation(id: "dio-class-orders", title: "Orders of mixed ideal classes", src: "20.5")[
  Assuming GRH for the class group computations: for all odd composite
  non-square $x$ up to $200 thin 001$ and five windows near $2.5$, $4$,
  $5.5$, $7$ and $8.5 dot 10^5$, the
  order $d$ of a mixed ideal class divides $x$ for some ideal in 6.5% of
  the $x$ below $10^4$ and 0.37% near $8.5 dot 10^5$. The share falls like
  $6.7 x^(-0.54)$. The smallest case is $x = 15$, $d = 3$, and the largest
  $d$ found is $34 thin 333$ at $x = 514 thin 995 = 15 dot 34 thin 333$.
]

#heuristic(id: "dio-loophole", title: "The class group cannot close the loophole", src: "20.5")[
  Extrapolating these statistics, the number of $x$ in
  $(4 dot 10^9, X]$ that pass every class-group condition of @cor-x-x grows
  like $10^4 ln(X slash (4 dot 10^9))$, without bound. Each such $x$ still
  needs the linear form to be smaller than $tau_x$, a chance of order
  $x^(-x slash 2)$. So the expected number of further solutions is far
  below 1, and a proof must use the Diophantine condition.
]

== Other exponents and the abc conjecture <sec-dio-exponents>

For small fixed $n$ the equation $U^2 = 4 x^n + x^2 + 4$ is a curve, and
the theory of curves applies (@app-curves).

#proposition(id: "dio-n2", title: [Exponent $n = 2$], src: "16.2")[
  $b(b + x) = x^2 + 1$ has a solution exactly when $5 x^2 + 4$ is a square,
  that is when $x$ is a Fibonacci number $F_(2k)$ of even index.
]

#computation(id: "dio-n3", title: [Exponent $n = 3$], src: ("16.2", "18.1"))[
  With $X = 4x$ and $Y = 4U$, $n = 3$ gives the elliptic curve
  $Y^2 = X^3 + X^2 + 64$, of conductor 433 and rank 2. It has exactly 10
  integral points, and they give $x in {3, 5, 8, 64, 119}$. This list is
  complete for all $x$.
]

#computation(id: "dio-n5", title: [Exponent $n = 5$], src: "18.1")[
  $b(b + x) = x^5 + 1$ has no solution with $x <= 10^(10)$. The curve
  $b^2 + x b = x^5 + 1$ has genus 2 and conductor $800 thin 027$, and its
  Jacobian has analytic rank 3. For $n = 7, 9, dots, 15$ the only solution
  with $x <= 10^9$ is $(7, 7)$, and for odd $n$ from 17 to 201 there is none
  with $x <= 10^8$.
]

For each $n >= 5$ the curve has genus at least 2, so Faltings's theorem
@faltings1983 gives finitely many solutions. But for $n = 5$ the known
methods do not finish the job. Chabauty and Coleman's method needs a
Mordell-Weil rank below the genus, and quadratic Chabauty needs rank equal
to the genus. Here the rank is probably 3, larger than the genus 2. What
remains is Baker's method for integral points on hyperelliptic curves with
the Mordell-Weil sieve @bmsst2008, which needs a saturated basis of the
Mordell-Weil group. So the case $n = 5$ is decidable but not decided.

Uniformly in $n$, the abc conjecture (@app-abc) gives finiteness.

#proposition(id: "dio-abc", title: "Solutions are abc triples of high quality", status: "proven", src: ("16.2", "18.1"))[
  For odd $x$, a solution of $b(b + x) = x^n + 1$ gives the coprime triple
  $(x^2 + 4) + 4 x^n = (2b + x)^2$. For $n = x$ its quality is at least
  $ln(4 x^x) slash ln(2x(x^2 + 4)(2 x^(x slash 2) + 1))$, which exceeds
  1.6299 for $x >= 29$ and tends to 2. With the sieve, any further solution
  with $n = x$ has quality above $2 - 10^(-8)$.
]

The best known abc triple, $2 + 3^(10) dot 109 = 23^5$ found by Reyssat,
has quality 1.6299 @granville-tucker2002.

#theorem(id: "dio-abc-finite", title: "Finiteness under abc", status: "conditional", src: ("16.2", "18.1"))[
  Assume the abc conjecture, or even its weak form
  $c < K op("rad")(a b c)^(2 - delta)$ for some $delta > 0$. Then
  $b(b + x) = x^n + 1$ has only finitely many solutions with $n >= 4$. In
  particular $b(b + x) = x^x + 1$ has only finitely many solutions.
]
#sketch[
  The radical of the triple is below $8.1 x^(3 + n slash 2)$. The weak abc
  inequality then bounds $x$ once $n > 12 slash delta - 6$, and the
  remaining exponents are finitely many curves of genus at least 2, each
  with finitely many points by Faltings's theorem. For $x equiv 0 med (mod 8)$
  divide the triple by 4 first.
]

This is the same status as Brocard's problem $n! + 1 = m^2$, where abc
gives finiteness @overholt1993, but here much less than abc suffices.

#heuristic(id: "dio-region", title: "The unsearched region", src: "18.1")[
  Given $x$ and $n$, the number $4 x^n + x^2 + 4$ is a square with chance
  about $1 slash (4 x^(n slash 2))$. Summed over the region not yet
  searched, the expected number of further solutions is below $10^(-14)$.
]

== The even case <sec-dio-even>

@dio-elementary leaves even $x$ open only when $x equiv 0 med (mod 8)$, and
@thm-prime-powers handles $x = 2^a$. So write $x = 2^a m$ with $a >= 3$ and
$m > 1$ odd, and let $n >= 5$ be odd. Put $V = b + x slash 2$ and
$E = (x slash 2)^2 + 1$, so that $V^2 - E = x^n$, and
$gamma = (V + sqrt(E)) slash 2$ in the order $R = ZZ[(1 + sqrt(E)) slash 2]$.
Then $N(gamma) = 2^(a n - 2) m^n$.

#lemma(id: "dio-even-ideal", title: [The ideal of $gamma$], src: "20.3")[
  The prime 2 splits in $R$, and
  $(gamma) = Q^(a n - 2) B^n$ with $Q$ one of the two primes above 2 and
  $B$ a product of primes above the primes of $m$.
]

Here the method of @sec-dio-field breaks: the exponent $a n - 2$ of $Q$ is
not a multiple of $n$. And $Q$ itself is far from principal.

#lemma(id: "dio-even-q", title: [Small powers of $Q$ are not principal], src: "20.3")[
  $Q^j$ is not principal for $1 <= j <= log_2 x - 3$.
]
#proof[
  If $Q^j = (pi)$ with $pi = (u + v sqrt(E)) slash 2$, then
  $|u^2 - E v^2|$ is $2^j$ or $2^(j+2)$ with $u$, $v$ coprime, and it is
  below $sqrt(E)$. A coprime solution of $|u^2 - E v^2| < sqrt(E)$ comes
  from a convergent of $sqrt(E)$ @niven-zuckerman-montgomery1991. But
  $sqrt(E) = [x slash 2; x, x, x, dots]$, and every convergent has norm
  $plus.minus 1$.
]

So a solution gives a linear form in three logarithms: the fundamental
unit, a generator of a power of the class of $Q^a B$, and a fixed number
$lambda$ that need not lie in the lattice of the other two. Laurent's
two-logarithm theorem no longer applies, and the general theorem of Matveev
@matveev2000 must be used. It has much larger constants.

#theorem(id: "dio-even-bound", title: [A bound for $n$], src: "20.3")[
  Let $x equiv 0 med (mod 8)$ have an odd prime factor, $n >= 5$ odd, $b$ a
  solution, and $d$ the order of the class of $Q^a B$. Then
  $n < 4.1 dot 10^(12) (d + 1)^2 (ln x)^2 (1 + ln n)$ for $x >= 24$.
]

Only one pure configuration gives a bound in the other direction, the
exponential $x < 2^(2n + 1)$, an analogue of $x < 11 n$ in
@dio-pure-lower #lib("20.3").

#computation(id: "dio-even-data", title: [The even case for small $x$], src: "20.3")[
  Let $x equiv 0 med (mod 8)$ have an odd prime factor and not be a square.
  For $x <= 10^8$ there is no solution with $n in {5, 7, dots, 15}$. For
  $x <= 10^4$ there is no solution with any odd $n >= 5$: 1,219 values of
  $x$ and 6,794 configurations, each reduced with the lemma of Dujella and
  Petho @dujella-petho1998.
]

== The families $(1, x, 2)$ and $(1, x, 3)$ <sec-dio-c>

Under $0^0 = 1$ the strings $(1, x, 2)$ and $(1, x, 3)$ lead to
$b(b + x) = x^x + 3$ and $b(b + x) = x^x + 25$. A neighbouring family is
easier.

#proposition(id: "dio-12x", title: [The family $(1, 2, x)$], src: "20.4")[
  $(1, 2, x)$ is a solution in some base exactly for $x = 6$, in base 215,
  under either convention.
]
#proof[
  The condition is $(b + 1)^2 = x^x + 6 - x$. For odd $x$,
  $x^x equiv x med (mod 8)$, so the right side is $6 med (mod 8)$, not a
  square. For even $x >= 8$ it lies strictly between
  $(x^(x slash 2) - 1)^2$ and $(x^(x slash 2))^2$. For $x = 6$ it is
  $6^6 = 216^2$, and the small cases fail by hand.
]

For $c = 3$ and $c = 25$ put $D = x^2 + 4c$ and $theta = (x + sqrt(D)) slash 2$,
of norm $-c$. Then $N(b + theta) = b^2 + b x - c$, so the equation says
$N(b + theta) = x^n$ in the order $ZZ[theta]$. Now $theta$ is not a unit.
Does the method of @sec-dio-field depend on the unit $epsilon$?

#lemma(id: "dio-c-elementary", title: "Elementary cases", src: "20.4")[
  Let $c in {3, 25}$ and $n >= 2$. There is no solution with $n >= 4$ even
  or with $n >= 5$ and $x$ a square, except $(x, n, b) = (3, 6, 26)$ for
  $c = 25$. For $c = 3$, $x$ is prime to 3 and every odd prime factor of
  $x$ is $plus.minus 1 med (mod 12)$.
]

=== $c = 25$: an explicit generator

For $c = 25$ and $x$ odd and prime to 5, the prime 5 splits, $(theta) = q^2$
for a prime $q$ above 5, and $(theta - 5) = q P$ with $N(P) = x$. Then
$P^2$ has the explicit generator
$
  pi = sqrt(D) - 10 = (theta - 5)^2 / theta,
$
and $|pi slash pi'| = e^(-2 ell)$ with $ell = op("arcsinh")(10 slash x)$. This
plays the role of $epsilon + 1$: a fixed power of the ideal of norm $x$ with
a generator whose logarithm is about $C slash x$ #lib("20.4").

#proposition(id: "dio-c25-pure", title: [Pure solutions for $c = 25$], src: "20.4")[
  Let $x$ be odd and prime to 5, $n >= 5$ odd ($n >= 7$ if $x = 3$), and
  $b$ a pure solution of $b(b + x) = x^n + 25$. Put $D = x^2 + 100$ and
  $tau_n = sqrt(D) slash (x^(n slash 2) - x slash 2 - 25)$. Then
  $|n ell - s mu_0| < tau_n$ for an integer
  $s >= 1$, so $n > (mu_0 - tau_n) x slash 10$. For odd $x >= 22 thin 027$
  prime to 5 there is no pure solution with $n = x$.
]

The second statement is easier than its analogue for $c = 1$: every unit
$e > 1$ of $ZZ[theta]$ satisfies $e > x$, so $mu_0 > ln x > 10$, while
$x ell < 10$.

#theorem(id: "dio-1x3", title: [The family $(1, x, 3)$ for prime powers], src: "20.4")[
  Under $0^0 = 1$, $(1, x, 3)$ is a solution in no base for any prime power
  $x$. For an odd prime power $x$, the solutions of $b(b + x) = x^n + 25$
  with $n >= 3$ are exactly $(x, n, b) = (5, 3, 10), (7, 3, 16), (3, 6, 26)$.
]
#sketch[
  Even $x$ and squares are elementary. Powers of 5 are handled through the
  continued fraction of $sqrt(y^2 + 4)$ with $y = x slash 5$. For other odd
  prime powers every solution is pure; Laurent's theorem bounds pure
  solutions for $x > 507 thin 211$, a computation with exact regulators
  covers smaller $x$, and sieves cover $n <= 15$.
]

=== $c = 3$: where the method stops

For $c = 3$ no element of $ZZ[theta]$ with a norm of the form
$plus.minus x^j 3^i 2^h$ is known uniformly in $x$, because that would need
a square root of 3 modulo $x$ given by a polynomial in $x$. So only the
analogue of @dio-mixed remains. In @sec-dio-baker the fundamental unit was
at most $epsilon$, so $mu_0 <= ln epsilon approx ln x$. For $c = 3$ there is
no unit of that size, and the regulator $mu_0$ is typically of size
$sqrt(D) approx x$.

#proposition(id: "dio-c3", title: "The regulator obstacle", src: "20.4")[
  Let $x > 10^6$ be prime and $b$ a solution of $b(b + x) = x^x + 3$, with
  $(b + theta) = p^x$. Then either the class number of $ZZ[theta]$ is a
  multiple of $x$, or $p$ is principal and
  $mu_0 (ln x + mu_0) > x ln x slash (202 M^2)$ with
  $M = max(ln(2x) + 0.38, 5)$.
]

The second case is the generic one: of the 1,121 primes
$x equiv plus.minus 1 med (mod 12)$ below $2 dot 10^4$, 621 have a principal
prime above $x$, and all of them have a regulator above this bound
(computed under GRH) #lib("20.4").

#computation(id: "dio-c-data", title: [The families for small $x$], src: "20.4")[
  $4 x^x + x^2 + 12$ and $4 x^x + x^2 + 100$ are not squares for
  $2 <= x <= 10^9$. For odd $x <= 1001$, $b(b + x) = x^n + 3$ has no
  solution with $n >= 2$, and $b(b + x) = x^n + 25$ with $x$ prime to 5 has
  only $(7, 3, 16)$ and $(3, 6, 26)$. For $n = 3$ the elliptic curves
  $Y^2 = X^3 + X^2 + 64 c$ give no solution for $c = 3$ and the solutions
  $(x, b) = (5, 10), (7, 16), (656, 16477), (1600, 63205)$ for $c = 25$.
]

The lesson of this section: the method of @sec-dio-baker does not need a
unit of norm $-1$. It needs a fixed power of the ideal of norm $x$ with an
explicit generator whose logarithm is about $C slash x$. For $c = 25$ that
generator exists; for $c = 3$ it does not, and the regulator then blocks
the argument even for prime $x$.

== Cores in perfect-power bases <sec-dio-cores>

The abc conjecture also controls a related question from
@ch-constructions. Under $0^0 = 0$ every solution splits into a core,
self-paying digits and an optional final 1 (@thm-structure-m0). Can a
nonzero core sit in a base with a self-paying digit, that is in a perfect
power? The swaps $(a, a^a)$ of @sec-cons-swaps give infinitely many such
cores #lib("15.3"). The question is whether anything else does.

#computation(id: "dio-cores-data", title: "Two-digit cores in perfect-power bases", src: "15.3")[
  Among the 2-digit solutions with $a <= 200$ and $c <= 3000$ under
  $0^0 = 0$, other than $(a, 0)$ and $(a, 1)$, exactly four have a
  perfect-power base: $(1, 3)$ in $5^2$ and the swaps $(2, 4)$ in $2^7$,
  $(3, 27)$ in $3^(80)$ and $(4, 256)$ in $2^(2046)$.
]

#theorem(id: "dio-cores-abc", title: "Cores under abc", status: "conditional", src: "15.3")[
  Assume the abc conjecture and fix $delta > 0$. Only finitely many 2-digit
  solutions $(a, c)$ under $0^0 = 0$ with $c >= 2$, $c != a^a$ and a
  perfect-power base satisfy
  $min(a^a, c^c) <= max(a^a, c^c)^(1 slash 4 - delta)$.
]
#sketch[
  Say $c^c > a^a$, and write the base as $r^t$ with $t >= 2$, so
  $r <= sqrt(b)$. The equation $a r^t = c^c + (a^a - c)$ is an abc sum
  whose radical is at most about $c^(c slash 2)$ times a power of the small
  term. abc then bounds $c$. The other case is symmetric.
]

The theorem leaves out the balanced case $a^a approx c^c$, where four large
terms appear (#q(37)). Part of one family is settled unconditionally: the
case $t | c$ of $(1, c)$. It does not cover $(1, 3)$ in base $25 = 5^2$,
where $t = 2$ does not divide $c = 3$.

#proposition(id: "dio-cores-1c", title: [The family $(1, c)$], src: "15.3")[
  For $t | c$, the base $c^c - c + 1$ of $(1, c)$ is not a $t$-th power.
]
#proof[
  With $Y = c^(c slash t)$ the base lies strictly between $(Y - 1)^t$ and
  $Y^t$, because $Y^t - (Y - 1)^t >= Y^(t-1) >= c^(c slash 2) > c - 1$.
]

Heuristically the number of perfect powers among the 2-digit bases is
$sum_((a, c)) b^(-1 slash 2)$, which converges fast. So the swaps and
$(1, 3)$ in base 25 are probably all 2-digit cores in perfect-power bases.
