#import "../template.typ": *

= Short solutions and the Munchausen polynomial <ch-short>

A solution with few digits is a different object from a solution with about
$b$ digits. For a long solution the base is fixed first and the digits must
conspire. For a short one it is natural to fix the digits first and ask for
the base. By @thm-one-base a digit string $s$ with at least two digits is a
solution in at most one base, namely a root of one polynomial. This chapter
studies that polynomial.

Fix a digit string $s = (s_1, dots, s_k)$, most significant first. Its value
polynomial and its _Munchausen polynomial_ are
$
  P_s (r) = s_1 r^(k-1) + s_2 r^(k-2) + dots + s_k,
  quad quad
  Q_s (r) = P_s (r) - F(s).
$
The string $s$ is a solution in base $b$ exactly when $Q_s (b) = 0$ and $b$
exceeds every digit of $s$. So $Q_s$ is a polynomial of degree $k - 1$ with
integer coefficients, and the short solutions are its integer roots above
the largest digit. Everything in this chapter comes from that one sentence:
complete lists found by solving for the base, local obstructions modulo
primes and prime powers, Galois groups, a heuristic for how often a root is
an integer, and the roots that are not ordinary bases.

== The complete lists <sec-short-lists>

Solving for the base turns the search around. Enumerate digit strings, and
for each one find the integer root of $Q_s$, if any. The root is found
exactly with integer arithmetic: $P_s$ is increasing and convex for
$r >= 0$, so Newton's method from above cannot jump over it.
By @thm-digit-bound a $k$-digit solution in base $b$ only uses digits $x$
with $x^x < b^k$. So the strings with digits up to $M$ contain every
$k$-digit solution in every base $b$ with $b^k <= (M + 1)^(M + 1)$. The
range of a list therefore grows like $M^(M slash k)$, very fast in $M$.

The Rust program `kdigit` does this with a sieve that rejects almost every
string before the exact step (@sec-short-local and @sec-search-short).
The lists below are exhaustive within their ranges.

#computation(id: "short-lists-m1", title: [Short solutions under $0^0 = 1$], src: ("3.2", "11.5", "19.1"))[
  Under $0^0 = 1$, the solutions with 3 to 8 digits in all bases up to the
  stated bound are exactly those of @tab-short-m1.
]

#tablefig(caption: [All solutions with 3 to 8 digits under $0^0 = 1$. A list
  with digits up to $M$ is complete for every base $b$ with
  $b^k <= (M+1)^(M+1)$.], id: "tab-short-m1")[
  #btable(
    columns: 4,
    align: (right, right, left, left),
    [$k$], [digits up to], [complete for bases up to], [solutions (base: digits)],
    [3], [80], [$10^(51.5)$], [4: $(1,3,1)$, $(3,1,3)$; 25: $(5,1,3)$; 91: $(6,1,5)$; 215: $(1,2,6)$; 904: $(1,7,1)$],
    [4], [300], [$10^(186.5)$], [10: $(3,4,3,5)$; 20: $(6,5,3,4)$],
    [5], [80], [$10^(30.9)$], [6: $(2,2,3,5,2)$, $(2,3,4,5,2)$; 7: $(1,3,4,5,4)$; 13: $(3,3,6,6,1)$; 14: $(2,6,0,3,6)$; 48: $(3,8,6,2,0)$],
    [6], [40], [$10^(11.0)$], [9: $(1,5,6,2,6,2)$],
    [7], [32], [$10^(7.2)$], [9: $(1,6,5,6,5,4,7)$],
    [8], [24], [$23 thin 364 approx 10^(4.4)$], [11: $(1,8,4,5,3,2,7,8)$, $(1,8,4,5,3,4,8,7)$],
  )
]

So 3435, the famous example, is one of exactly two 4-digit solutions in all
bases up to $10^(186)$. The other is $(6, 5, 3, 4)$ in base 20:
$6 dot 20^3 + 5 dot 20^2 + 3 dot 20 + 4 = 50 thin 064 = 6^6 + 5^5 + 3^3 + 4^4$.
A separate search over 3-digit strings with two digits up to 1000 and the
third up to 30 reaches bases near $10^(1500)$ and finds the same six
3-digit solutions #lib("16.1").

Under $0^0 = 0$ the lists are infinite, because of the self-paying digits of
@sec-cons-selfpaying. A digit $x$ with $x^(x-1) = b^(k-1)$ gives the two
solutions $(x, 0, dots, 0, 0)$ and $(x, 0, dots, 0, 1)$ in base $b$. Apart
from these families the lists are short.

#computation(id: "short-lists-m0", title: [Short solutions under $0^0 = 0$], src: ("3.3", "19.1"))[
  Under $0^0 = 0$, in the ranges of @tab-short-m1, the solutions with 3 to 8
  digits are the self-paying families and the strings of @tab-short-m0.
]

#tablefig(caption: [Solutions with 3 to 8 digits under $0^0 = 0$ that are
  not of the form $(x, 0, dots, 0, e)$ with $x$ self-paying. Same ranges as
  @tab-short-m1. Swaps and other constructions of @ch-constructions are
  marked.], id: "tab-short-m0")[
  #btable(
    columns: 2,
    align: (right, left),
    [$k$], [solutions (base: digits)],
    [3], [4: $(1,3,0)$, $(1,3,1)$, $(3,1,3)$; 5: $(1,0,3)$; 25: $(5,1,3)$; 91: $(6,1,5)$; 215: $(1,2,6)$; 904: $(1,7,0)$, $(1,7,1)$; $3^(40)$: $(3,0,27)$ (swap)],
    [4], [5: $(2,0,2,4)$; 10: $(3,4,3,5)$; 20: $(6,5,3,4)$; 128: $(8,0,2,4)$ (self-paying 8 on the swap $(2,4)$); $2^(682)$: $(4,0,0,256)$ (swap; this base, about $10^(205.3)$, lies outside the complete range)],
    [5], [6: $(2,2,3,5,2)$, $(2,3,4,5,2)$; 7: $(1,3,4,5,4)$; 11: $(6,6,5,0,0)$, $(6,6,5,0,1)$; 13: $(3,3,6,6,0)$, $(3,3,6,6,1)$; $3^(20)$: $(3,0,0,0,27)$ (swap)],
    [6], [9: $(1,5,6,2,6,2)$; 11: $(5,1,7,5,0,3)$; $3^(16)$: $(3,0,0,0,0,27)$ (swap), $(3,0,0,0,9,27)$ (swap with the self-paying 9)],
    [7], [9: $(1,6,4,7,0,6,3)$, $(1,6,5,6,5,4,7)$],
    [8], [9: $(3,4,6,6,4,0,8,4)$; 11: $(1,8,4,5,3,2,7,8)$, $(1,8,4,5,3,4,8,7)$],
  )
]

@app-tables lists every string, the families included. Two-digit solutions
are plentiful under both conventions and have a complete description
(@thm-two-digit), so this chapter starts at three digits.

=== Which lengths occur

Under $0^0 = 0$ every length occurs, in infinitely many bases
(@thm-every-length-m0). Under $0^0 = 1$ the searches show gaps.

#computation(id: "short-missing-lengths", title: "Missing lengths", src: ("3.4", "11.4"))[
  Under $0^0 = 1$ no base up to $100 thin 000$ has a solution with 9 digits,
  and no base up to $10 thin 000$ has one with 18, 21, 22, 24, 26 or 28
  digits. Among the lengths 2 to 30, these 7 are the only ones without a
  solution in any base up to 127.
]

For a large length the model of @ch-model expects about one solution of
that length over all bases together, so a length is empty with probability
about $e^(-1) approx 37%$. The data show 7 empty lengths out of 29, or 24%.
These lengths are not empty for ever, though. The binomial families of
@thm-binomial give solutions of every length $k >= 3$ under $0^0 = 1$
(@thm-every-length-m1), in bases far beyond any search: the smallest
3-digit member after $(1, 2, 6)$ is $(1, 6, 46666)$ in base
$46666^(23333) - 3$, about $10^(108942)$.

#remark(id: "short-finiteness-remark", src: ("3.5", "7.2", "22.3"))[
  The library first conjectured that under $0^0 = 1$ each length $k >= 3$
  has only finitely many solutions. The evidence was the lists above and the
  spacing heuristic of @sec-short-heuristic, which predicts a finite total
  for every $k >= 3$. The binomial families refute the conjecture. They are
  instructive: a heuristic that treats the root of $Q_s$ as a random real
  number cannot see a family whose polynomial factors by an identity. What
  survives is a question (#q(64)): is every short solution beyond some size
  a member of an algebraic family?
]

== Local obstructions <sec-short-local>

A polynomial with an integer root has a root modulo every integer. Turned
around, this is a cheap test that rejects strings in every base at once.

#proposition(id: "thm-local", title: "Local obstruction", src: ("11.3", "19.1"))[
  If the polynomial $Q_s$ of a digit string $s$ has no root modulo some
  integer $q >= 2$, then $s$ is not a solution in any base.
]
#proof[
  If $Q_s (b) = 0$, then $b mod q$ is a root of $Q_s$ modulo $q$, because
  $Q_s$ has integer coefficients and $Q_s (r) mod q$ depends only on
  $r mod q$.
]

Two facts limit the useful moduli. By the Chinese remainder theorem, $Q_s$
has a root modulo $q_1 q_2$ with $gcd(q_1, q_2) = 1$ exactly when it has a
root modulo $q_1$ and modulo $q_2$. And a root modulo $p^e$ reduces to a
root modulo $p^f$ for $f < e$. So only one power of each prime adds
information, and a higher power makes the lower ones redundant
#lib("19.1").

How often does a random polynomial have no root? Over a large prime field,
inclusion and exclusion over the roots shows that a random polynomial of
degree $n$ has no root with probability
$
  sum_(j = 0)^n (-1)^j / j! quad -> quad e^(-1) approx 0.368,
$
which is $1 slash 2$, $1 slash 3$, $3 slash 8$ and $11 slash 30$ for
$n = 2, 3, 4, 5$, the degrees $k - 1$ for $k = 3, dots, 6$ #lib("19.1").
The large primes of the sieve match these values to within 0.004 (@tab-short-moduli). @sec-short-galois explains why:
the Galois group of $Q_s$ is almost always the full symmetric group, and the
share of permutations without a fixed point is exactly this sum.

#tablefig(caption: [Share of candidate strings that one modulus removes when
  it is tested first #lib("19.1"). $k$ digits, digits up to $M$.],
  id: "tab-short-moduli")[
  #btable(
    columns: 5,
    align: (left, right, right, right, right),
    [modulus], [$k = 3$, $M = 80$], [$k = 4$, $M = 44$], [$k = 5$, $M = 28$], [$k = 6$, $M = 16$],
    [2], [0.012], [0.030], [0.055], [0.092],
    [32], [0.286], [0.218], [0.298], [0.336],
    [3], [0.204], [0.229], [0.253], [0.281],
    [27], [0.386], [0.350], [0.391], [0.417],
    [5], [0.306], [0.318], [0.326], [0.328],
    [25], [0.416], [0.362], [0.403], [0.402],
    [127], [0.496], [0.333], [0.373], [0.366],
    [random, large $p$], [$1 slash 2$], [$1 slash 3$], [$3 slash 8$], [$11 slash 30$],
  )
]

The small primes are weak tests, and the reason is the digit-sum identity
of @thm-digit-sum. At $r equiv 1$ the value $Q_s (1) = sum_i (s_i - w(s_i))$
vanishes modulo $p$ for many strings. Modulo 2 it is worse.

#proposition(id: "short-mod2", title: "The test modulo 2", src: "15.4")[
  $Q_s$ has no root modulo 2 exactly when both parity rules of
  @sec-basics-congruences fail for $s$: $Q_s (1)$ odd excludes every odd
  base, and $Q_s (0)$ odd excludes every even base.
]
#proof[
  $Q_s (0) = s_k - F(s)$ and $Q_s (1) = sum_i s_i - F(s)$. For odd $b$,
  $Q_s (b) equiv Q_s (1)$, and for even $b$, $Q_s (b) equiv Q_s (0)$ modulo 2.
]

Since $x^x equiv x med (mod 2)$, the last digit moves $Q_s$ only by even
amounts modulo 2. Modulo $2^e$ the even digits $x >= e$ have
$x^x equiv 0$, so the test sees the value of $x$ itself. That is why 32
removes 3 to 25 times as much as 2. The powers of 3 gain for a reason explained
in @sec-short-coverings: the values of $x^x - x$ modulo 27 fill only 10
residues.

=== The sieve

The test splits over positions. Fix the first $k - 1$ digits. For a modulus
$q$, the values of the prefix part of $Q_s (r)$ over all residues $r$ form
a bit mask, and the last digit $x$ passes if the residue it needs lies in
the mask. So the test costs a few bit operations per string and modulus.
Only the strings that pass every modulus go on to the exact root.

#computation(id: "short-sieve", title: "Survivors of the sieve", src: ("11.5", "19.1"))[
  With the moduli 32, 27, 25, 49 and the primes 11 to 127, the sieve passes
  36,309 of the $4.1 dot 10^(10)$ strings with 7 digits up to 32, and
  133,240 of the $1.5 dot 10^(11)$ strings with 8 digits up to 24. With the
  18 primes up to 61 alone the share was $3$ to $6 dot 10^(-4)$, close to
  the $0.632^18 = 2.6 dot 10^(-4)$ that independent tests would give.
]

The near-independence of the primes has a good explanation. For 3-digit
strings with digits up to 80, the product of the measured survival shares
predicts 28.9 survivors. Eleven further strings have a rational root and
pass every test by definition. That makes about 40, against 46 observed
#lib("11.5"). @sec-search-short describes the program and its speed.

== Coverings and the residues of $x^x - x$ <sec-short-coverings>

Local tests can do more than reject one string. Fix all digits but one and
let that digit $x$ vary. Whether $Q_s$ has a root modulo $q$ then depends
only on $x$ modulo a period, because $x^x mod q$ is periodic in $x$. If the
residues excluded by several moduli cover all integers, the whole infinite
family is excluded in every base. This is the idea of the covering
congruences behind the Sierpinski numbers.

A varying last digit enters $Q_s$ as $x - x^x$. So the set
$
  T(q) = { x^x - x mod q : x >= 1 }
$
decides which coverings exist. If $T(q)$ is all of $ZZ slash q$, the
modulus $q$ can never exclude a last digit on its own.

#lemma(id: "short-tq-small", title: "Small moduli", src: ("15.4", "20.2"))[
  + For $q = 2^e$, $T(q)$ is the set of even residues.
  + For a prime $p >= 5$, $T(p) = ZZ slash p$. And $T(3) = {0, 2}$.
  + If $x equiv 2 med (mod 6)$, then $x^x - x equiv 2 med (mod 27)$.
    Otherwise $x^x - x equiv 0 med (mod 3)$. So $T(9) = {0, 2, 3, 6}$ and
    $T(27) = 3 ZZ slash 27 union {2}$.
]
#proof[
  (1) $x^x equiv x med (mod 2)$, and even $x >= e$ give $x^x equiv 0$, so
  $-x$ runs over all even residues.
  (2) Modulo $p$, $x^x$ depends on $u = x mod p$ and $j = x mod (p - 1)$,
  which are independent by the Chinese remainder theorem. The residue 0
  comes from $x equiv 0 med (mod p)$. For a target
  $v != 0$, pick a primitive root $u != -v$; then $u + v$ is a unit, so
  $u + v = u^j$ for some $j$, and the matching $x$ gives $x^x - x equiv v$.
  A prime $p >= 5$ has at least two primitive roots.
  (3) Only $x equiv 2 med (mod 6)$ gives $x^x equiv.not x med (mod 3)$.
  Put $u = -x = 1 + 3t$. Since $x$ is even, $x^x = u^x$, and the binomial
  theorem modulo 27 gives
  $x^x - x equiv 2 + (x + 1)^3 (x - 2) slash 2 med (mod 27)$, with
  $27 | (x + 1)^3$.
]

#theorem(id: "thm-covering", title: "Covering by 27", src: "15.4")[
  Let $A(r) = sum_(i=1)^(k-1) s_i r^(k-i)$ and $F_0 = sum_(i=1)^(k-1) w(s_i)$
  for a prefix $(s_1, dots, s_(k-1))$. If $A(r) - F_0 equiv.not 0 med (mod 3)$
  and $A(r) - F_0 equiv.not 2 med (mod 27)$ for every residue $r$ modulo 27,
  then no string $(s_1, dots, s_(k-1), x)$ with $x >= 1$ is a solution in
  any base, under either convention. Under $0^0 = 0$ this also holds for
  $x = 0$.
]
#proof[
  A solution in base $b$ gives $A(b) - F_0 = x^x - x$, and by
  @short-tq-small the right side is $0 med (mod 3)$ or $2 med (mod 27)$.
]

#example(id: "short-21x", src: "15.4")[
  For the prefix $(2, 1)$, $A(r) - F_0 = 2 r^2 + r - 5$. Modulo 3 it takes
  the values 1, 1, 2 at $r = 0, 1, 2$. For $r equiv 2 med (mod 3)$,
  $2 r^2 + r$ is 1 or 10 modulo 27, never 7. So $(2, 1, x)$ is not a
  solution for any $x >= 1$, in any base. The digit $x$ can be as large as we
  like, so this excludes bases up to infinity in one stroke.
]

#computation(id: "short-cover-search", title: "Coverings are common", src: ("15.4", "20.2"))[
  Among the 3-digit families with fixed digits up to 10, 27 of 341 are
  covered under $0^0 = 1$, and 22 of them need a modulus other than 2. For
  random prefixes with digits in $[3, 10^6]$, the last digit is excluded in
  every base for 11.2% of 3-digit prefixes and 7.2% to 8.6% of prefixes
  with 4 to 6 digits, using the moduli 16, 27, 25 and 7. The modulus 27
  alone gives 11.2% and 7.2% to 8.4%, so almost all of this comes from
  @thm-covering. Adding
  the modulus 81 raises the shares by 0.2 to 0.4 percentage points.
]

So about one prefix in twelve makes its last digit impossible in every
base. The minimal sets of moduli found are mostly $\{4\}$, $\{9\}$, $\{3\}$
and $\{3, 4\}$; one covering, of $(2, 0, 1, 0, x)$ under $0^0 = 1$, needs
8, 11 and 25 together #lib("15.4").

=== The laws of $x^x - x$ modulo prime powers

The covering theorem rests on the gaps of $T(27)$. Which other prime powers
have gaps? For $p >= 7$ none do, and for 3 and 5 the gaps follow explicit
laws. The tool is the $p$-adic exponential (@app-padic).

#lemma(id: "short-lift", title: "Lifting", src: "20.2")[
  Let $p$ be odd and $x_0$ prime to $p$ with $x_0^(x_0) equiv.not 1 med (mod p)$.
  As $x$ runs over the integers with $x equiv x_0 med (mod p(p-1))$, the
  value $x^x - x$ modulo $p^e$ runs over the whole class
  $x_0^(x_0) - x_0 + p ZZ$, for every $e >= 1$. Multiples of $p$ also lie in
  $T(p^e)$ for every $e$.
]
#sketch[
  Step from $x$ to $x' = x + p^(j+1)(p-1) s$. Then
  $x'^(x') equiv x^x (1 + p^(j+1)(p-1) s) med (mod p^(j+2))$, so
  $x^x - x$ moves by $p^(j+1)(p-1)(x^x - 1) s$, and $x^x - 1$ is a unit. So
  the step $s$ runs through every value of the next $p$-adic digit.
  Induction on $j$. For the multiples of $p$, take $x equiv 0 med (mod p)$
  with $x >= e$: then $x^x - x equiv -x$.
]

#theorem(id: "short-tq-large", title: "Primes from 7 on", src: "20.2")[
  For every prime $p >= 7$ and every $e >= 1$, $T(p^e) = ZZ slash p^e$.
]
#sketch[
  By @short-lift it suffices to reach every nonzero residue $v$ modulo $p$
  with some $x$ whose $x^x equiv.not 1$. Take a primitive root $u$ that
  avoids $-v$ and $1 - v$; then $u + v$ is a power $u^j != 1$. For
  $p >= 11$ there are at least four primitive roots, and $p = 7$ is checked
  by hand.
]

For $p = 3$ and $p = 5$ some classes have $x^x equiv 1 med (mod p)$, the
step of @short-lift vanishes, and the class does not lift freely. On such a
class write $x = zeta e^a$ with $zeta$ a root of unity in $ZZ_p$ and
$a in p ZZ_p$. Then $x^x = exp(zeta a e^a)$ when the order of $zeta$
divides $x$, and $x^x - x$ becomes a power series in $a$ with explicit
coefficients #lib("20.2").

#theorem(id: "short-3adic", title: "The 3-adic law", src: "20.2")[
  For $e >= 4$,
  $
    T(3^e) = { v : v equiv 0 med (mod 3) } union { v : v equiv 2 med (mod 27), thick v equiv.not 56 med (mod 81) }.
  $
  So $T(3^e)$ has density $29 slash 81$, and for $e >= 5$ it is the full
  preimage of $T(81)$.
]
#sketch[
  Only the class $x equiv 2 med (mod 6)$ matters. With $zeta = -1$ and
  $a = 3w$, the values are $2 + 27 G(w)$ with a power series $G$ whose
  coefficients lie in $ZZ_3$ and tend to 0. Modulo 3,
  $G(w) equiv -(w^3 + w^4)$, which takes the values 0, 1, 0 at
  $w equiv 0, 1, 2$. So $G$ never takes the value 2 modulo 3, which
  excludes $v equiv 56 med (mod 81)$. The derivative is a unit at
  $w equiv 1, 2$, and Hensel's lemma shows that every other value is
  reached modulo every $3^e$.
]

#theorem(id: "short-5adic", title: "The 5-adic law", src: "20.2")[
  Let $i$ be the square root of $-1$ in $ZZ_5$ with $i equiv 3 med (mod 5)$,
  and $A = 1 - i$. For $e >= 2$,
  $
    T(5^e) = { v : v equiv.not 3 med (mod 5) } union { A (1 - 25 s slash 2) mod 5^e : s "a square in" ZZ_5 }.
  $
  The class $3 med (mod 5)$ holds 1, 3, 11, 53, 261, 1303 elements of
  $T(5^e)$ for $e = 2, dots, 7$, and the density of $T(5^e)$ tends to
  $49 slash 60$.
]

The laws were checked against direct computation of $T(3^e)$ for
$e <= 10$ and $T(5^e)$ for $e <= 7$ #lib("20.2"). They have two consequences
for coverings.

#corollary(id: "short-81", title: "81 is the last useful power of 3", src: "20.2")[
  If $A(r) - F_0 in.not T(81)$ for every residue $r$ modulo 81, then no
  string $(s_1, dots, s_(k-1), x)$ with $x >= 1$ is a solution in any base.
  For a single modulus $3^e$ with $e >= 5$ this test excludes nothing new.
]

For example, 81 excludes $(8, 7, x)$ for every $x$, and 27 does not: the
value $8 r^2 + 7 r - 8^8 - 7^7$ is $2 med (mod 27)$ only for
$r equiv 8 med (mod 9)$, and there it is $56 med (mod 81)$.

#proposition(id: "short-5power", title: "Single powers of 5", src: "20.2")[
  If a single modulus $5^e$ excludes every last digit of a prefix, then
  every digit of the prefix is a multiple of 5, or the polynomial $A mod 5$
  is a nonzero multiple of $(r^5 - r)^2$ and the prefix has at least 10
  digits.
]

So the 5-adic gaps matter only together with other moduli. The prime powers
$2^e$ and $3^e$ carry the coverings, because of the coupling between
$x mod 3^e$ and $x mod 2 dot 3^(e-1)$. An open question (#q(38)) asks
whether every covering needs a modulus on which $x^x - x$ misses residues,
that is a power of 2 or 3, or a power of 5 from 25 on.

== Galois groups and reducibility <sec-short-galois>

How strong is the local test in the limit? A string that passes the test for
every prime is either a solution or a string whose polynomial has a very
special shape. This section makes that precise. @app-galois explains the
tools: the Galois group of a polynomial, the Chebotarev density theorem and
Jordan's theorem.

=== The Galois group is the full symmetric group

For a polynomial of degree $n$ with Galois group $G$, the Chebotarev density
theorem says that the share of primes $p$ modulo which it has no root equals
the share of elements of $G$ that fix no root. For $G = S_n$ this is the
share of derangements, $sum_(j <= n) (-1)^j slash j!$.

#computation(id: "short-chebotarev", title: "Root-free primes", src: "12.1")[
  For 60 random strings of each length $k = 3, 4, 5, 6$ (digits up to 20,
  $0^0 = 1$), the share of primes from 200 to $20 thin 000$ modulo which
  $Q_s$ has no root has median 0.501, 0.335, 0.374 and 0.367. The
  derangement shares of $S_(k-1)$ are 0.500, 0.333, 0.375 and 0.367.
]

So $Q_s$ generically has the full symmetric Galois group, as Hilbert's
irreducibility theorem leads one to expect: the constant term $F(s)$ is
unrelated to the other coefficients. The one exception among the 240
strings is $(9, 18, 18, 9, 15)$, with a share of 0.631. Its value polynomial
satisfies $P_s (r) - 15 = 9 r (r + 1)(r^2 + r + 1) = 9 u (u + 1)$ with
$u = r^2 + r$. So $Q_s$ is a
polynomial in $r^2 + r$, its group lies in the dihedral group $D_4$, and the
derangement share of $D_4$ is $5 slash 8$. Decomposable value polynomials
are the natural source of smaller groups.

=== The local test is complete for irreducible polynomials

#proposition(id: "short-irreducible", title: "Irreducible polynomials fail locally", src: "12.2")[
  If $Q_s$ is irreducible of degree $n >= 2$, then $Q_s$ has no root modulo
  $p$ for a set of primes $p$ of density at least $1 slash n$.
]
#proof[
  The Galois group acts transitively on the roots. By Jordan's theorem a
  transitive group contains an element that fixes no root, and Cameron and
  Cohen @cameron-cohen1992 proved that such elements make up at least a
  share $1 slash n$ of the group. The Chebotarev density theorem turns this
  share into a density of primes (@app-galois).
]

So a string that passes the test for every prime has a reducible $Q_s$. A
polynomial with a root modulo almost every prime but no rational root is
called _intersective_. The question is whether some $Q_s$ is intersective.

#proposition(id: "short-intersective-5", title: [No intersective polynomial for $k <= 5$], src: "16.3")[
  If $k <= 5$ and $Q_s$ has a root modulo all but finitely many primes, then
  $Q_s$ has a rational root.
]
#proof[
  Without a rational root, $Q_s$ is irreducible, or for $k = 5$ a product of
  two irreducible quadratics with fields $QQ(sqrt(D_1))$ and
  $QQ(sqrt(D_2))$. The irreducible case is @short-irreducible. If the two
  fields are equal, the primes inert in it (density $1 slash 2$) give no
  root. If they differ, the primes inert in both (density $1 slash 4$) give
  no root.
]

#proposition(id: "short-intersective-6", title: [The criterion for $k = 6$], src: "16.3")[
  A quintic $Q_s$ has a root modulo almost every prime but no rational root
  exactly when $Q_s = g h$ with $g$ an irreducible quadratic, $h$ an
  irreducible cubic with group $S_3$, and
  $QQ(sqrt(op("disc") g)) = QQ(sqrt(op("disc") h))$.
]

The classic example $(x^3 - 19)(x^2 + x + 1)$ has this shape, so the
question for six digits is real. No string with digits up to 9 gives one
#lib("16.3").

=== Reducibility for five digits

For $k = 5$ a factorization into two quadratics can be analysed by
comparing coefficients. Write $a, b', c, d$ for $s_2, s_3, s_4, s_5$
divided by $s_1$, and let $q = c - a b' slash 2 + a^3 slash 8$. Then $q = 0$
exactly when $P_s (r)$ is a polynomial in $(r + a slash 4)^2$, that is,
when $P_s$ is decomposable.

#theorem(id: "short-k5-reducible", title: "Two quadratic factors", src: "16.3")[
  Let $k = 5$ and let the largest digit be at least 3. If $Q_s$ is a product
  of two quadratics over $QQ$, then $q = 0$, so $P_s$ is decomposable.
  Hence $Q_s$ is reducible exactly when it has a rational root, or when
  $P_s = s_1 G((r + a slash 4)^2)$ and the resulting quadratic in
  $(r + a slash 4)^2$ splits in a suitable way.
]
#sketch[
  Comparing coefficients expresses $F slash s_1$ through the coefficients
  and one parameter $tau$, with a term $q^2 slash (4 tau^2)$. Gauss's lemma
  makes $2 s_1 tau$ an integer, so if $q != 0$ the formula bounds $F$ by a
  polynomial of degree 7 in the largest digit $M$. But $F >= M^M$. For
  $M >= 7$ this is a contradiction, and an exact check covers
  $3 <= M <= 12$.
]

#theorem(id: "short-galois-45", title: "Galois groups for four and five digits", src: "16.4")[
  + For $k = 4$ and largest digit $M >= 5$, every irreducible $Q_s$ has
    Galois group $S_3$.
  + For $k = 5$ and $M >= 6$, every irreducible $Q_s$ has group $S_4$,
    unless $P_s$ is decomposable, and then the group lies in $D_4$.
]
#sketch[
  Once $F > (M + 1)^k$, $Q_s$ has exactly one real root for $k = 4$ and two
  for $k = 5$, because $P_s$ has no critical point outside
  $|r| <= M + 1$. For $k = 4$ the group $A_3$ needs three real roots. For
  $k = 5$ complex conjugation is a transposition, so the group is $S_4$ or
  $D_4$, and $D_4$ needs a rational root of the resolvent cubic. That root
  satisfies an equation that is linear in $F$ and bounds $F$ unless $q = 0$.
]

#computation(id: "short-galois-data", title: "Smaller groups", src: "16.4")[
  For $k = 4$ with digits up to 10, all 26,580 irreducible $Q_s$ have group
  $S_3$. For $k = 5$ with digits up to 8, 1,967 have group $D_4$, all with
  decomposable $P_s$, and 102,865 have $S_4$. For $k = 6$ with digits up to
  5, 81 have the Frobenius group of order 20 and the rest $S_5$. The 81
  are $s_1 r^5 + s_6$ and the strings $(1,0,5,0,5,x)$ and $(5,0,5,0,1,x)$,
  which are Dickson polynomials: $r^5 + 5 r^3 + 5 r = D_5(r, -1)$. These are
  the two exceptional families of Ritt's theory @ritt1922.
]

#computation(id: "short-reducible-67", title: "Six and seven digits", src: "16.3")[
  For $k = 6$ (digits up to 9) and $k = 7$ (digits up to 6), every
  factorization of $Q_s$ without a linear factor and without a
  decomposition of $P_s$ has largest digit at most 4. None of these
  polynomials has a root modulo every prime below 3000.
]

#conjecture(id: "short-conj-reducible", title: "Reducibility for large digits", src: "16.3")[
  For every $k$ there are constants $C_k$ and $c_k$ such that, once
  $F(s) > C_k M^(c_k)$, every factorization of $Q_s$ without a linear factor
  comes from a decomposition $P_s = G(h(r))$. (Question #q(33).)
]

If the conjecture holds, no $Q_s$ with large digits is intersective unless
$P_s$ is decomposable. The sieve agrees: of 400 sampled survivors of the 18
primes with 4 digits, 394 are irreducible and would fall to more primes,
and 6 have a rational root #lib("12.2").

== The root heuristic <sec-short-heuristic>

The probabilistic model of @ch-model treats each base on its own. For a
short string it is better to ask a different question: given $s$, is the real
root of $Q_s$ an integer? This section builds a heuristic for that question,
calibrates it, and explains what it cannot see.

=== Spacing

Let $s$ have $k$ digits and largest digit $x$. The real root $b^*$ of $Q_s$
is about $x^(x slash (k-1))$. As $s$ varies over strings with nearby roots,
$Q_s$ changes by integers, so the root moves in steps of about
$1 slash Q'_s (b^*)$. So the chance that $b^*$ is an integer is about
$1 slash Q'_s (b^*)$, roughly $x^(-x(k-2) slash (k-1))$. There are about
$k x^(k-1)$ strings with largest digit $x$.

#heuristic(id: "short-spacing", title: "Spacing heuristic", src: ("3.5", "11.4"))[
  The expected number of $k$-digit solutions is
  $E approx sum_s 1 slash Q'_s (b^*)$. It is finite for every $k >= 3$. For
  $k = 2$ the chance is about $1 slash a$ for the leading digit $a$, and the
  sum diverges.
]

The divergence for two digits is right: there are infinitely many 2-digit
solutions (@thm-two-digit). The finiteness for $k >= 3$ is wrong, as
@thm-every-length-m1 shows. We return to this below.

=== Local factors

A string whose polynomial has no root modulo $p$ cannot be a solution, and
a string with two roots modulo $p$ is twice as likely to have a root at a
random integer. So each prime contributes a factor, the number of roots.

#heuristic(id: "short-root-heuristic", title: "Root heuristic with local factors", src: ("11.4", "19.3"))[
  The expected number of $k$-digit solutions is
  $
    E = sum_s product_p N_s (p^e) / Q'_s (b^*),
  $
  capped at 1 per string, where $N_s (p^e)$ is the number of roots of $Q_s$
  modulo a high power $p^e$ of each small prime $p$.
]

The first version of the heuristic used the number $rho_s (p)$ of roots
modulo $p$. The right factor is the density of the event $p^e | Q_s (b)$
for a random integer $b$, divided by $p^(-e)$, which is $N_s (p^e)$. When
every root modulo $p$ is simple, Hensel's lemma gives $N_s (p^e) = rho_s (p)$.
A multiple root can lift to no root or to several.

#proposition(id: "short-average-one", title: "The local factor averages 1", src: "19.3")[
  Over a constant term that is uniform modulo $p^e$, the mean of
  $N_s (p^e)$ is exactly 1.
]
#proof[
  Each of the $p^e$ residues $r$ is a root for exactly one value of the
  constant term modulo $p^e$.
]

So the local factors move individual strings but not the average. The
factor stabilizes from $2^4$, $3^3$ and $5^2$ on.

#tablefig(caption: [The root heuristic under $0^0 = 1$ against the
  observed counts #lib("11.4", "19.3"). The heuristic sums over strings with
  digits up to the stated bound.], id: "tab-short-root")[
  #btable(
    columns: 6,
    align: (right, right, right, right, right, right),
    [$k$], [digits up to], [spacing only], [roots mod $p$], [roots mod $p^e$], [observed],
    [3], [60], [2.31], [5.09], [5.59], [6],
    [4], [22], [1.38], [1.39], [0.75], [2],
    [5], [11], [1.13], [2.42], [3.32], [6],
    [all], [], [4.82], [8.90], [9.66], [14],
  )
]

With local factors the 3-digit count matches. The 4-digit and 5-digit
counts rest on 2 and 6 data points, and single strings near the cap decide
them: 3435 has two roots modulo 2 but only one modulo 64, so its weight
drops from 1 to 0.49 #lib("19.3"). Better calibration needs more data, which
the offsets provide.

=== Calibration by offsets

A solution is a string with $P_s (b) - F(s) = 0$. A near-solution at offset
$D$ has $P_s (b) - F(s) = D$. Near-solutions are further draws of the same
kind of coincidence, so their counts calibrate the heuristic without
trusting it. The program `kdigit` takes an option `--offset D` for this.

#computation(id: "short-offsets-4", title: "Offsets for four digits", src: "19.2")[
  Under $0^0 = 1$, digits up to 22, the 200 offsets $D = 1, dots, 200$ have
  682 pairs $(s, b)$ in bases below 100. The heuristic predicts 731 with
  roots modulo $p$ and 677 with roots modulo $p^e$. The counts per offset
  have variance over mean 0.97, as for a Poisson law. Calibrated by the
  offsets, the expectation at $D = 0$ is 0.6 to 1.4, and 2 observed has
  probability 0.13 to 0.42.
]

Small offsets also catch neighbours of true solutions and algebraic
families. 3435 has the neighbours $(3, 4, 1, 5)$ at $D = 6$ and
$(3, 4, 2, 5)$ at $D = 13$. The string $(1, 0, 0, x)$ with $x^x$ a cube sits
at $D = x - 3$ in base $x^(x slash 3)$, and $(1, 3, 3, x)$ at $D = x - 56$
in base $x^(x slash 3) - 1$. These identities hold with certainty where they
hold, so the comparison above leaves out the bases of 100 and more, where
15 of 16 pairs belong to such families #lib("19.2").

For five digits the offsets agree with the heuristic in bases below 10, 354
against 353.7. In bases 10 to 99 they show about twice the predicted count,
mostly in clusters: groups of about four hits with a common prefix of three
digits. Some clusters come from exact
identities, such as $6 dot 11^4 + 6 dot 11^3 + 5 dot 11^2 = 6^6 + 6^6 + 5^5$,
the self-paying block of @sec-cons-blocks. The cleanest calibration is base
by base.

#computation(id: "short-calibration", title: "Base-by-base calibration", src: "22.4")[
  For each base $b$ and length $k$, count the strings with
  $P_s (b) - F(s) = D$ for all offsets $D$ in the class of 0 modulo
  $2(b - 1)$ with $b <= |D| <= 0.05 b^(k-1)$. The mean count per offset
  estimates the expected number of solutions in that base. For 5 digits in
  bases 13 to 99 this uses 1.24 million offsets with 257 hits and gives
  0.33, with a range of 0.26 to 0.49 over the choices of window and class.
  For 6, 7 and 8 digits in bases 3 to 12 it gives 1.19, 0.99 and 1.13
  against 1, 1 and 2 observed.
]

The 5-digit estimate agrees with the root heuristic, 0.28 with roots modulo
$p$ and 0.33 with roots modulo $p^e$. But bases 13 to 99 hold three 5-digit
solutions: $(3, 3, 6, 6, 1)$ in base 13, $(2, 6, 0, 3, 6)$ in base 14 and
$(3, 8, 6, 2, 0)$ in base 48.

#heuristic(id: "short-5-excess", title: "The 5-digit excess", src: ("19.2", "22.4"))[
  Three 5-digit solutions in bases 13 to 99 against 0.33 expected is an
  excess of about 9 times. Under a Poisson law the probability of 3 or more
  is 0.0047 (0.0024 to 0.014 over the choices of the calibration), and about
  0.015 after allowing for the choice among the 10 cells that were examined.
]

The excess was once put at 17 times, from a calibration by far offsets
$D = 75 thin 600 j$ with only 10 hits. The base-by-base calibration
replaces it #lib("22.4"). Could self-paying blocks explain the rest? The
first solution is the exact block $(3, 3, 6, 6)$ followed by a 1:
$13 dot P_((3,3,6,6))(13) = 93 thin 366 = 3^3 + 3^3 + 6^6 + 6^6$. But the
heuristic already counts this route.

#lemma(id: "short-block-route", title: "Blocks are inside the heuristic", src: "22.4")[
  Under $0^0 = 1$, the polynomial of the string $(t, 1)$ is
  $r P_t (r) - F(t)$, the polynomial of the block equation
  $b P_t (b) = F(t)$.
]
#proof[
  $P_((t, 1))(r) - F(t, 1) = r P_t (r) + 1 - F(t) - 1$.
]

The block route carries 0.039 of the expected 0.33, so blocks do not explain
the excess. It stays an unexplained fluctuation at the level of
$P approx 0.015$ #lib("22.4").

=== What the heuristic cannot see

The completeness of the lists can be estimated with the same heuristic: sum
the expected number of solutions with a digit above the list's bound.

#heuristic(id: "short-tails", title: "Completeness of the lists", src: ("11.4", "19.1"))[
  For strings without an algebraic identity, the expected number of
  solutions missing from the lists is about $10^(-74)$ for 3 digits,
  $10^(-490)$ for 4, $10^(-109)$ for 5, $10^(-45)$ for 6,
  $1.7 dot 10^(-33)$ for 7 and $5.7 dot 10^(-21)$ for 8. For the missing
  lengths 9, 18, 21, 22, 24, 26 and 28 it is $10^(-29)$ or less.
]

These numbers say nothing about algebraic families. In the binomial
family of @thm-binomial the digits are the coefficients of $(c r + e)^(k-1)$
without the constant term, followed by a digit $x$ with $x^x$ a
$(k-1)$-th power. For these strings
$
  Q_s (r) = (c r + e)^(k-1) - x^x
$
exactly, so the root is an integer by an identity. The heuristic gives such
a string the weight $1 slash Q'_s (b^*)$, which is astronomically small. The
same holds for the self-paying digits under $0^0 = 0$. So the refined
heuristic of #lib("22.4") adds the family members in a range, counted
exactly, to the calibrated mean. In the searched ranges no family member
under $0^0 = 1$ appears, and the tail estimates stand for generic strings.

== The square class and near-integers <sec-short-square>

When one digit $x$ is large, $F(s)$ is dominated by $x^x$, and the question
"is the root an integer?" becomes a question about how close a power comes
to an integer. One case can be settled completely.

#theorem(id: "thm-square-class", title: "Large leading digit", src: "8.2")[
  Fix $k >= 2$ and $k - 1$ lower digits below a bound $B$, and let the
  leading digit $x$ vary with $x^(x-1)$ a perfect $(k-1)$-th power. For $x$
  above an explicit bound that depends on $B$ and $k$, the only solutions
  are the self-paying families $(x, 0, dots, 0, 0)$ and
  $(x, 0, dots, 0, 1)$ under $0^0 = 0$, and $(x, 1)$ with $k = 2$ under
  $0^0 = 1$. For $k >= 3$ there are none under $0^0 = 1$.
]
#proof[
  Write $x^(x-1) = Z^(k-1)$, let $Q(b)$ be the value of the lower $k - 1$
  digits and $C$ the sum of their weights. The equation is
  $x b^(k-1) + Q(b) - C = x Z^(k-1)$, with $0 <= Q(b) < 2 B b^(k-2)$.
  If $b >= Z + 1$, the left side is at least
  $x Z^(k-1) + x(k-1) Z^(k-2) - C$, too large once $x(k-1) Z^(k-2) > C$.
  If $b <= Z - 1$, the left side is at most
  $x Z^(k-1) - (Z - 1)^(k-2)(x(k-1) - 2B)$, too small once
  $x(k - 1) > 2B$. So $b = Z$ and $Q(Z) = C$. A nonzero lower digit at a
  position $i >= 1$ gives $Q(Z) >= Z > C$ for large $x$. So the only nonzero
  lower digit is the last one, $e$, and $e = (k-2) w(0) + w(e)$. Under
  $0^0 = 0$ this means $e^e = e$, so $e in {0, 1}$. Under $0^0 = 1$ it means
  $e = k - 2 + w(e)$, and since $w(e) >= e$ this forces $k = 2$, $e = 1$.
]

=== Three digits: completing the square

For three digits $(p, q, r)$ the equation $p b^2 + q b + r = F$ becomes
$
  (2 p b + q)^2 = 4 p F + q^2 - 4 p r.
$
If one digit $x$ is large, write the right side as $4 p x^x + R$ when $x$
is not the leading digit (and similarly when it is). Call the string _in the
square class_ when the dominant term is a perfect square. Then the right
side is a square plus a term of size about $x^2$, and two squares that close
must be equal, which bounds $x$, unless $R = 0$.

#proposition(id: "short-r-zero", title: "When the remainder vanishes", src: "22.3")[
  Let one digit $x$ of a 3-digit string vary, under $0^0 = 1$. Then $R = 0$
  only if $x$ is the last digit and $x = p^p + q^q + q^2 slash (4p)$. If
  moreover $x$ is even, then $p = c^2$ is a square, $q = 2 c e$, and the
  solutions are exactly the members of the binomial families
  (@thm-binomial) with $j = 2$.
]

#remark(id: "short-cor84", src: ("8.2", "22.3"))[
  An earlier corollary in the library claimed that the 3-digit solutions
  with two digits at most 20 and the third in its square class are the known
  ones. It assumed $R != 0$. With @short-r-zero the correct statement adds
  8 binomial members, $(1, 6, x)$, $(1, 10, x)$, $(1, 14, x)$, $(1, 18, x)$,
  $(4, 8, x)$, $(4, 16, x)$, $(9, 6, x)$ and $(9, 18, x)$, all in bases above
  $10^(108942)$.
]

=== Outside the square class

When the dominant term is not a square, write $4 p x^x = N Y^2$ with $N$
squarefree. The equation asks whether $4 p x^x + R$ is a square: a
Pell-type equation $U^2 - N Y^2 = R$ with the extra condition that $Y$
equals a prescribed number such as $x^((x-1) slash 2)$ (@app-quadratic). For
each single $x$ this is decidable. For all $x$ at once it asks whether an
exponentially growing sequence ever lands on the solution set of a Pell
equation that itself changes with $x$. For longer strings it asks whether
$x^((x-1) slash (k-1))$ comes within about $B slash x$ of an integer.

Such questions are beyond current methods. Even for the single sequence
$(3 slash 2)^n$ it is unknown whether the fractional parts are dense in
$[0, 1]$. Mahler @mahler1957 proved that $(3 slash 2)^k$ stays at
distance more than $c^k$ from the nearest integer for every $c < 1$ and
large $k$, without an effective bound, and Zudilin @zudilin2007 gave the
effective constant 0.5803. No published result handles equations where
the base and the exponent of $x^x$ vary together #lib("8.2", "9.10").

#computation(id: "short-near-integer", title: "The near-integer law", src: "12.5")[
  Fix two digits of a 3-digit string and let the third, $x$, run over odd
  values up to 6,001, under $0^0 = 1$. For $(x, 1, 5)$, in the square class,
  the real root $b^*(x)$ sits just below an integer, with
  $x norm(b^*(x)) = 0.500$ for every $x$ from 19 to 6,001. For $(1, x, 1)$,
  $(6, 1, x)$ and $(2, x, 3)$ the fractional parts look uniform: 1.8% to
  2.1%, 9.7% to 10.2% and 48.5% to 49.6% of them lie below 0.01, 0.05 and
  0.25. The only exact hits are the known solutions.
]

So in the square class the root approaches the integers without reaching
them, which is @thm-square-class seen numerically. Outside it the root
behaves like a random number. That is what the spacing heuristic assumes,
but a solution needs $b^*(x)$ to be an integer to within $x^(-x slash 2)$,
far below what such a test can resolve. The family $(1, x, 1)$ leads to the
equation $b(b + x) = x^x + 1$, the subject of @ch-diophantine.

== Almost all bases have no short solution <sec-short-almost-all>

The lists of @sec-short-lists are complete only up to a bound. Counting
arguments say something about all bases: short solutions exist only in a
sparse set of bases. Recall that $X_k (b)$ is the largest digit $x$ with
$x^x < b^k$. For fixed $k$, $X_k (b) tilde k ln b slash ln(k ln b)$.

#proposition(id: "short-per-base", title: "Few short solutions per base", src: "4.1")[
  $N_(m, k)(b) <= 2 (X_k (b) + 1)^(k-1)$. For fixed $k$ this is a power of
  $log b$.
]
#proof[
  Every digit is at most $X_k (b)$ (@thm-digit-bound). Fix the last $k - 1$
  digits. The leading digit $a$ must satisfy $a^a - a b^(k-1) = R$ with $R$
  fixed. The left side is strictly convex in $a$, so at most two values of
  $a$ work.
]

#proposition(id: "short-bases-k", title: "Few bases per length", src: "10.5")[
  The number of bases up to $B$ with a $k$-digit solution is at most
  $X (X + 1)^(k-1)$, where $X = X_k (B)$.
]
#proof[
  Every digit is at most $X$, and each digit string is a solution in at most
  one base (@thm-one-base).
]

Counting multisets instead of strings saves a factor of about $k!$. The
price is that a multiset does not fix the base, but a window around a known
value does.

#lemma(id: "short-window", title: "The base window", src: "20.1")[
  Let $n$ be a solution in base $b$ with $k >= 2$ digits, leading digit $p$
  and largest digit $M$. Then
  $
    b <= (n slash p)^(1 slash (k-1)) < b + (M + 1) / (p (k - 1)).
  $
]
#proof[
  The second digit is at most $M$ and the rest add at most
  $b^(k-2) - 1$, so $p b^(k-1) <= n < p b^(k-1) + (M + 1) b^(k-2)$. Take
  $(k-1)$-th roots and use Bernoulli's inequality.
]

All 3,135 known solutions satisfy the window, and it is close to sharp: the
largest relative position of $(n slash p)^(1 slash (k-1))$ in it is 0.984
#lib("20.1"). A multiset $c$ determines $n = F(c)$, the leading digit is one
of its digits, and the window then holds at most $M + 2$ candidate bases.

#proposition(id: "short-multiset-count", title: "Counting multisets", src: "20.1")[
  Let $k >= 2$ and $X = X_k (B)$. Under a fixed convention, the number of
  bases $b <= B$ with a $k$-digit solution is at most
  $
    binom(X + k, k) ( (X + 1) H_k / (k - 1) + k ),
  $
  where $H_k = 1 + 1 slash 2 + dots + 1 slash k$.
]

#theorem(id: "thm-almost-all", title: "Almost all bases", src: ("20.1", "11.6"))[
  For every $epsilon > 0$, almost all bases $b$ have no solution with
  $2 <= k <= (1 - epsilon) ln b slash ln ln b$ digits, under either
  convention. More precisely, with $L = ln B$ and fixed $alpha < 1$, at most
  $B^(alpha + o(1))$ bases $b <= B$ have a solution with at most
  $alpha L slash ln L$ digits. The same holds for $k$ up to
  $
    (ln b) / (ln ln b) (1 + (ln ln ln b + ln 2 - 1 - delta) / (ln ln b))
  $
  for any fixed $delta > 0$, and no argument that counts multisets reaches
  further.
]
#sketch[
  Put $K = kappa L slash ln L$ and $X = X_K (B)$. From $X^X approx B^K$ one
  gets $ln(X slash K) = ln L - ln ln L - ln 2 + o(1)$, so $X$ is about
  $kappa L^2 slash (2 (ln L)^2)$ and $K^2 slash X$ is bounded. Stirling's
  formula then gives
  $ln binom(X + K, K) = kappa L (1 - a slash ln L + dots)$ with
  $a = ln ln L + ln 2 - 1$. The other factors of @short-multiset-count and
  the sum over $k <= K$ cost only $exp(O(ln L))$. With $kappa = alpha$ the
  count is $B^(alpha + o(1))$. The sharper range comes from taking
  $kappa = 1 + (a - delta) slash ln L$, and the same computation with
  $+delta$ shows that the bound for $k = K$ alone then exceeds $B$.
]

The first version of this theorem counted strings and reached only
$(1 slash 2 - epsilon) ln b slash ln ln b$ #lib("11.6"). Counting multisets
doubles the range.

#computation(id: "short-b96", title: [The bounds at $B = 10^96$], src: "20.1")[
  At $B = 10^96$, where $L slash ln L = 40.95$, the string bound stays below
  $B$ up to 31 digits and the multiset bound up to 49 digits. At 16 digits
  the bounds are $B^(0.458)$ and $B^(0.343)$.
]

The theorem is weak in absolute terms. It covers lengths of order
$ln b slash ln ln b$, while the model of @ch-model puts almost all solutions
near $b$ digits. It is the first unconditional statement that solutions are
absent from most bases in a whole range of lengths.

For a fixed length the multiset count alone is weaker than
@short-bases-k, because each window holds about $X slash (p k)$ integers.
The digit-sum identity repairs this: $b - 1$ divides $F(c) - S(c)$, where
$S(c)$ is the digit sum of $c$ (@thm-digit-sum).

#lemma(id: "short-divisors", title: "Divisors in a short interval", src: "20.1")[
  Let $d_1 < dots < d_r$ be divisors of $m >= 1$ in an interval $(Y - h, Y]$
  with $Y - h >= 1$. Then $m > (Y - h)^r slash h^(r(r-1) slash 2)$.
]
#proof[
  $m$ is a multiple of $op("lcm")(d_1, dots, d_r)$, which is at least
  $product_i d_i slash product_(i < j) gcd(d_i, d_j)$ by a count of prime
  exponents. Each $gcd(d_i, d_j)$ divides $d_j - d_i < h$.
]

#proposition(id: "short-fixed-k", title: "Fixed length", src: "20.1")[
  For $k >= 3$ the number of bases $b <= B$ with a $k$-digit solution is at
  most $X^k slash (k - 2)! (1 + o(1))$ as $B -> infinity$, with
  $X = X_k (B)$. This improves @short-bases-k by the factor $(k - 2)!$.
]

Beyond $alpha = 1$ any argument that tests candidates one at a time stops,
because the number of multisets itself exceeds $B$. Going further would need
an equidistribution statement: that the integers
$F(c) - S(c) = sum (d^d - d)$ spread evenly over residue classes modulo the
integers $b - 1$ of a short window that depends on $F(c)$ itself. No method
for this is known #lib("20.1").

== Other roots: negative bases and rational roots <sec-short-roots>

$Q_s$ has integer roots that are not ordinary bases. Some are Munchausen
numbers in negative bases; others are too small to be bases. Rational roots
pass every local test, which is why the local test can never prove alone that
a string fails everywhere.

=== Negative bases

In base $-b$ with $b >= 2$, every integer has exactly one representation
with digits 0 to $b - 1$ and no sign (@app-numeration). So a string with
digits below $b$ is a Munchausen number in base $-b$ when
$Q_s (-b) = 0$: an integer root of the same polynomial at $r < -max(s)$.
@sec-worlds-negative has the census and the model. Two facts belong here.

#proposition(id: "short-odd-length", title: "Odd length", src: "12.3")[
  A Munchausen number in a negative base has an odd number of digits.
]
#proof[
  Its value $F(s)$ is positive. A string of length $k$ in base $-b$ with a
  nonzero leading digit has the sign of $(-b)^(k-1)$, because the leading
  term outweighs all others. So $k - 1$ is even.
]

#proposition(id: "short-partners", title: "Partners", src: "12.3")[
  Let $(s_1, s_2, s_3)$ be a solution in base $b$ with $s_1 | s_2$. Then it
  is also a solution in base $-(b + s_2 slash s_1)$.
]
#proof[
  The two roots of the quadratic $Q_s$ add up to $-s_2 slash s_1$, so the
  other root is the integer $-b - s_2 slash s_1$. Its absolute value
  exceeds $b$, which exceeds every digit.
]

The 3-digit solutions with leading digit 1, namely $(1, 3, 1)$ in base 4,
$(1, 2, 6)$ in base 215 and $(1, 7, 1)$ in base 904, have the partners
$-7$, $-217$ and $-911$. A fourth negative-base solution, $(1, 1, 1)$ in
base $-2$, has the partner root 1, which is not a base. With five digits,
$(1, 3, 4, 3, 3)$ is a solution in base $-5$:
$625 - 375 + 100 - 15 + 3 = 338 = 1 + 27 + 256 + 27 + 27$.

#computation(id: "short-nonpartner", title: "Non-partners", src: ("16.6", "18.4"))[
  Among all 3-digit strings with digits up to 200, and those with two digits
  up to 1000 and one up to 30, the only negative-base solution under
  $0^0 = 1$ that is not a partner is $(1, 1, 1)$ in base $-2$.
]

For five digits partners need a symmetry of the value polynomial.

#theorem(id: "short-partners-5", title: "Partners with five digits", src: "16.6")[
  Let $k$ be odd and let $s$ be a solution in base $b$ and in base $-c$.
  Then $c >= b$ and $delta = c - b < 4M slash s_1$. If
  $P_s (r) != P_s (-r - delta)$, then $b <= 1 + 2 k M (1 + delta)^(k-1)$,
  which for $k = 5$ forces $M <= 30$. If $P_s (r) = P_s (-r - delta)$, then
  $P_s = G(r^2 + delta r)$ and every solution in base $b$ is also one in base
  $-(b + delta)$.
]

Under $0^0 = 1$ no 5-digit string with digits up to 300 is a solution in
both a positive and a negative base #lib("16.6").

=== Signs of the roots

Positive bases have three 3-digit solutions without a partner:
$(3, 1, 3)$ in base 4, $(5, 1, 3)$ in base 25 and $(6, 1, 5)$ in base 91.
Negative bases have none apart from $(1, 1, 1)$. Is something suppressing
negative roots?

#proposition(id: "short-sign-symmetry", title: "The heuristic is symmetric", src: "18.4")[
  The root heuristic with local factors gives the two roots of every 3-digit
  string the same weight.
]
#proof[
  The local factors depend only on $Q_s$, and the derivative at the two
  roots has the same absolute value $sqrt(Delta)$, where $Delta$ is the
  discriminant.
]

Inside the square class the symmetry breaks. If the leading digit $p$ is odd
and the largest digit, then $sqrt(Delta) = Y + t$ with $Y$ divisible by
$2p$, and the positive root is an integer when $t equiv q med (mod 2p)$,
the negative root when $t equiv -q$. For $0 < q < p$ the smallest
admissible $t$ is $q$ for the positive root and $2p - q$ for the negative
one #lib("18.4").

#heuristic(id: "short-sign-bias", title: "Positive roots are favoured in the square class", src: "18.4")[
  For square-class strings with the largest digit in front, small values of
  $t$ make the positive root about 9 times as likely as the negative one:
  0.0564 against 0.0064 expected solutions with digits up to 70. Outside the
  square class the weights are equal.
]

$(5, 1, 3)$ and $(3, 1, 3)$ follow this mechanism: for $(5, 1, 3)$,
$Y = 250$ and $t = 1 = q$. The third non-partner, $(6, 1, 5)$, is an
ordinary coin flip that came up positive.

=== Roots that are too small, and rational roots

An integer root $r$ with $|r|$ at most the largest digit is a valid identity
$P_s (r) = F(s)$ in a representation whose digits are too large. Examples
under $0^0 = 1$: $(3, 1, 2)$ at $r = 3$, where $27 + 3 + 2 = 32 = 27 + 1 + 4$,
and $(4, 1, 3, 1)$ at $r = 4$. With digits up to 28 there are 32 such
5-digit strings #lib("12.4"). They pass every local test. So the bound
$r > max(s)$ must come from outside the local theory.

#proposition(id: "short-rational", title: "Rational roots of quadratics", src: "16.5")[
  If $Q_s$ with $k = 3$ has a rational root $p slash q$ in lowest terms, its
  other root $p' slash q'$ is rational with $q q' = s_1$, and the two roots
  have opposite signs.
]
#proof[
  By Gauss's lemma $Q_s = (q r - p)(q' r - p')$ over $ZZ$. The product of the
  roots is $(s_3 - F) slash s_1 < 0$.
]

#computation(id: "short-rational-data", title: "Rational roots", src: "16.5")[
  For $k = 3$ with digits up to 80 and $k = 4$ with digits up to 44, no $Q_s$
  has a non-integer rational root above its largest digit. For $k = 3$ the
  non-integer rational roots that occur are the negative partners of the
  positive solutions with $s_1 divides.not s_2$, such as $-13 slash 3$ for
  $(3, 1, 3)$, together with a few small ones.
]

So rational roots are rarer than integer roots. The meaningful version of a
"rational base" is the number system of Akiyama, Frougny and Sakarovitch,
treated in @sec-worlds-rational.

== Bases with a 2-digit and a 3-digit solution <sec-short-two-three>

Two-digit solutions are plentiful and short ones are rare. Can one base
have both?

#lemma(id: "short-two-digit-size", title: "Two-digit bases are large", src: "18.2")[
  If base $b$ has a 2-digit solution $(a, c)$ under $0^0 = 1$ and
  $m = max(a, c)$, then $b >= m^(m-1)$. So a base below $10^(460)$ with a
  2-digit solution has digits at most 200 in it.
]
#proof[
  By @thm-two-digit, $b = (a^a + g(c)) slash a$ with $g(c) = w(c) - c >= 0$.
  If $a = m$, then $b >= a^(a-1)$. If $c = m > a$, then
  $b >= (c^c - c) slash (c - 1) >= c^(c-1)$. Finally $201^(200) > 10^(460)$.
]

#computation(id: "short-base25", title: "Base 25 is alone", src: "18.2")[
  Under $0^0 = 1$, base 25 is the only base below $10^(51)$ with both a
  2-digit and a 3-digit solution, $(1, 3)$ and $(5, 1, 3)$. Among the 8,502
  bases of 2-digit solutions with digits up to 200, which include every such
  base below $10^(460)$, base 25 is the only one with a 3-digit solution.
  Under $0^0 = 0$ the same holds below $10^(51)$ and for the bases of
  2-digit solutions with digits up to 120.
]

Base 25 works by a coincidence between powers. It is $3^3 - 3 + 1$, the
base of $(1, 3)$, and it is $5^2$, which makes 5 self-paying at position 2:
$5 dot 25^2 = 5^5$. So $(5, 1, 3)$ is the self-paying 5 on top of the
2-digit solution $(1, 3)$. The two descriptions meet because
$3^3 - 2 = 5^2$, the same coincidence that gives $(1, 0, 3)$ in base 5
under $0^0 = 0$.

Base 4 has two 3-digit solutions, $(1, 3, 1)$ and $(3, 1, 3)$. Every other
base below $10^(51)$ has at most one.

#problem(id: "short-q50", title: "At most two 3-digit solutions", src: "18.2")[
  Under $0^0 = 1$, does every base have at most two 3-digit solutions?
  (Question #q(50).) In one base each leading digit $p$ allows at most two
  values of the largest digit. When the largest digit is not the leading
  one, this leaves at most two strings per leading digit. But a base has
  many possible leading digits, so this alone does not bound the count by
  two, and when the largest digit leads, up to $p$ strings remain.
]
