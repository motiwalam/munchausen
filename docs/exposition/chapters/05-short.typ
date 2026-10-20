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
  $b^k <= (M+1)^(M+1)$. For 3 digits a sharper argument gives a larger range
  (@short-3digit-range).], id: "tab-short-m1")[
  #btable(
    columns: 4,
    align: (right, right, left, left),
    [$k$], [digits up to], [complete for bases up to], [solutions (base: digits)],
    [3], [2000], [$10^(3301)$], [4: $(1,3,1)$, $(3,1,3)$; 25: $(5,1,3)$; 91: $(6,1,5)$; 215: $(1,2,6)$; 904: $(1,7,1)$],
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
  @tab-short-m1, except that the 3-digit list is complete only for bases up
  to $10^(51.5)$ (digits up to 80). Swaps and other constructions of @ch-constructions are
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

=== Three digits up to $10^(3301)$

For three digits the range of the list is much larger, because a sieve with
many primes is cheap and a direct bound replaces the general one.

#computation(id: "short-3digit-range", title: "The 3-digit list", src: "25.2")[
  Under $0^0 = 1$:
  + every 3-digit solution in a base up to $10^(3301)$ is one of the six of
    @tab-short-m1;
  + every 3-digit solution in a base below $46666^(23333) - 3$ with at most
    one digit above 200 is one of these six.
  So a 3-digit solution in a base strictly between 904 and
  $46666^(23333) - 3$ has two digits above 200, one digit above 2000, and a
  base above $10^(3301)$.
]

The method is the completed square of @sec-short-square. A string
$(p, q, r)$ is a solution exactly when $D = 4p(F - r) + q^2$ is a square
$s^2$ and $b = (s - q) slash (2p)$ is an integer above the digits. A program
tests $D$ for quadratic residues modulo the 108 odd primes below 600, with
tables of $w(d)$ modulo each prime, and checks the survivors exactly. Part 1
takes all strings with digits up to 2000: a solution with a digit
$M > 2000$ has $b^2 > M^M slash (M + 1) >= 2001^(2001) slash 2002$, so every
base below $10^(3301.2)$ is covered. Part 2 takes all strings with two
digits up to 200 and one up to 46,700. In all $1.36 dot 10^(10)$ strings
were tested, and only 12 survived all 108 primes. Seven of them are
solutions: the six known ones and $(1, 6, 46666)$. The other five have a
root that is not an integer, or an integer root at most the largest digit
#lib("25.2").

The binomial families of @sec-cons-binomial give infinitely many 3-digit
solutions beyond this range. Their members are the strings
$(lambda c^2, 2 lambda c e, x)$ of case (i) of @short-three-digit-class
below, and they can be listed in order.

#proposition(id: "short-members-order", title: "Members in order", src: "25.2")[
  Among the 3-digit members of the binomial families, a larger last digit
  $x$ gives a larger base.
]
#sketch[
  A member has $b <= sqrt(x^x slash lambda) <= x^(x slash 2)$. For a member
  with last digit $x' >= x + 1 >= 7$, the other digits are at most
  $sqrt(x')$, so its base is at least $x'^((x'-1) slash 2) - x'$, and
  Bernoulli's inequality shows that this exceeds $x^(x slash 2)$.
]

By this ordering and a short case check, the next member after $(1, 2, 6)$
in base 215 is $(1, 6, 46666)$ in base $46666^(23333) - 3$
(@cons-next-member).

#computation(id: "short-members-list", title: "The first members", src: "25.2")[
  The strings with $p, q <= 2000$ contain every 3-digit member with
  $x < 2001^(2001) approx 10^(6605.8)$. There are 1,267 of them, all with
  $lambda = 1$ and even $x$. @tab-short-members lists the first five.
]

#tablefig(caption: [The first 3-digit members of the binomial families, in
  order of base #lib("25.2").], id: "tab-short-members")[
  #btable(
    columns: 4,
    align: (right, left, left, left),
    [rank], [$(p, q, x)$], [$(c, e)$], [base],
    [1], [$(1, 2, 6)$], [$(1, 1)$], [215],
    [2], [$(1, 6, 46666)$], [$(1, 3)$], [$46666^(23333) - 3 approx 10^(108941.8)$],
    [3], [$(4, 8, 16777476)$], [$(2, 2)$], [about $10^(10^(7.78))$],
    [4], [$(9, 6, 387467146)$], [$(3, 1)$], [about $10^(10^(9.22))$],
    [5], [$(1, 10, 10000000026)$], [$(1, 5)$], [about $10^(10^(10.70))$],
  )
]

#heuristic(id: "short-next-heuristic", title: "Nothing between", src: "25.2")[
  The strings that @short-3digit-range leaves open have a digit $M > 2000$
  and a second digit above 200. By the root heuristic each is a solution
  with probability about $M^(-M slash 2)$, and there are fewer than $3 M^2$
  of them for each $M$. The expected number of such solutions is below
  $3 dot 2000^2 dot 2000^(-1000) approx 10^(-3294)$.
]

So the claim "$(1, 6, 46666)$ is the next 3-digit solution after
$(1, 7, 1)$" has three parts. It is proven that $(1, 6, 46666)$ is the next
family member (@cons-next-member), and that it is the only 3-digit
solution in its base (@short-member-base). It is computed that no other
3-digit solution lies in bases from 905 to $10^(3301)$, nor below
$46666^(23333) - 3$ with at most one digit above 200. It is heuristic that
no string with two digits above 200 and one above 2000 fills the rest of the
gap. An exhaustive run over all strings with digits up to 46,700 would need
about $10^(14)$ tests and has not been done. Under an explicit form of the
abc conjecture, the strings with two digits at most 200 are settled in
every base (@short-abc-explicit).

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
  a member of an algebraic family? @cons-families-conj states the
  current conjecture.
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
    E = sum_s (product_p N_s (p^e)) / (Q'_s (b^*)),
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

=== Local factors and the per-base model <sec-short-arrangements>

The root heuristic gives each string a factor at every small prime. The
per-base model of @ch-model has only the factor of the identity modulo
$b - 1$ (@sec-model-refined). The two look like different heuristics. They
are one heuristic averaged in two ways, and the link is the way the
arrangements of one multiset spread over the residues modulo $q$.

Fix a base $b$, a modulus $q$ and a multiset $c$ of $k >= 3$ digits, and
draw an arrangement of $c$ with a nonzero leading digit uniformly. Write
$sigma(c)$ for the digit sum. If $q | b - 1$, every arrangement is
congruent to $sigma(c)$ modulo $q$ (@thm-digit-sum). If $q | b$, the
residue is fixed by the last digit. The remaining case is
$gcd(q, b(b - 1)) = 1$. Since $b (b - 1)$ is even, such a $q$ is odd.

#theorem(id: "short-thm-arrangements", title: "Arrangements spread over the residues", src: "35.1")[
  Let $gcd(q, b(b - 1)) = 1$. Fix the leading digit, let the other
  $k' = k - 1$ digits be $x_1, dots, x_(k')$, and put
  $
    gamma = max_(h equiv.not 0 med (mod q)) lr(|1 / k' sum_(i = 1)^(k') e(h x_i slash q)|).
  $
  Then for every residue $a$,
  $
    |q P(n equiv a med (mod q)) - 1| <= (q - 1) e^(1 slash 8) exp(-(1 - gamma)^2 (k - 1) slash 64).
  $
  The same holds without fixing the leading digit, with $gamma$ the largest
  over the leading digits.
]
#sketch[
  Pair the positions $(2j, 2j + 1)$. Exchanging the digits $u, v$ of a pair
  moves $n$ by $(v - u) b^(2j) (1 - b)$, a unit times $v - u$ modulo $q$.
  Exchange each pair or not by a fair coin. The arrangement stays uniform,
  and the coins multiply $E thin e(h n slash q)$ by factors
  $|cos(pi h delta_j slash q)|$. A pair is two distinct digits drawn from
  those not yet used, so the mean of $cos^2$ is at most
  $(1 + rho_j^2) slash 2$, with $rho_j$ close to $gamma$. Take about
  $(1 - gamma) k slash 8$ pairs and sum over $h$ #lib("35.1").
]

The rate depends on the length and on how spread out the digits are, not
on the order of $b$ modulo $q$, as question #q(91) expected. The proof
uses nothing about $b$ except that $b$ and $b - 1$ are units modulo $q$.
So it applies to every residue $r$ of the base with $r$ and $r - 1$ prime
to $q$.

#proposition(id: "short-prop-base-average", title: "The local factor is a base average", src: "35.1")[
  For a string $s$ let $N_s (q)$ be the number of residues $r$ modulo $q$
  with $P_s (r) equiv F(s) med (mod q)$. For every multiset $c$, the mean of
  $N_s (q)$ over the arrangements $s$ of $c$ is
  $
    sum_(r med (mod q)) P(P_s (r) equiv F(c) med (mod q)).
  $
  The term $r = 1$ is 1 if $q$ divides $F(c) - sigma(c)$ and 0 otherwise.
  The term $r = 0$ is the share of arrangements whose last digit is
  congruent to $F(c)$. For a prime $q$ each other term is $1 slash q$ up to
  the error of @short-thm-arrangements.
]
#proof[
  Exchange the sum over $r$ and the mean over the arrangements. Then
  $P_s (1) = sigma(c)$ and $P_s (0)$ is the last digit. For a prime $q$
  every other $r$ has $r$ and $r - 1$ prime to $q$.
]

So the local factor of a string, averaged over its arrangements, is the
per-base factor averaged over the residue of the base. The refined model
keeps the residue of the actual base: at bases $b equiv 1$ it has the
identity factor $q$ or 0, at the others the arrangement factor or the
last-digit factor. The two heuristics agree on totals over many bases and
differ base by base.

#computation(id: "short-comp-arrangements", title: "How fast the arrangement factors approach 1", src: "35.1")[
  Candidate multisets of $k$ digits in bases 9 to 30, 40 per base, under
  $0^0 = 1$, with the shares computed exactly. RMS of
  $q P(n equiv F(c)) - 1$ over the bases with $gcd(q, b(b - 1)) = 1$:

  #align(center, btable(
    columns: 7,
    align: (left, right, right, right, right, right, right),
    [$q$], [$k = 3$], [4], [6], [8], [10], [12],
    [3], [0.76], [0.59], [0.28], [0.17], [0.087], [0.043],
    [5], [0.93], [0.73], [0.30], [0.18], [0.082], [0.036],
    [7], [1.14], [0.71], [0.30], [0.21], [0.075], [0.040],
    [9], [1.48], [1.03], [0.51], [0.25], [0.12], [0.084],
  ))

  The spread falls like $e^(-0.35 k)$ and is below 0.1 from 10 digits on
  for $q = 3, 5, 7$ and from 12 digits on for $q = 9$. The mean of the
  factor is 0.98 to 1.04 in every cell from 5 digits on, and 0.87 to 1.05
  at 3 and 4 digits.
]

The arrangement factors have mean 1. They add scatter to single strings,
not an excess. So they cannot be why short solutions are more common than
the basic model of @ch-model says, which was the lead of question #q(91).
Part of the excess has another source. At a short length a sum of a few
values $x^x - x$ of small digits is concentrated modulo the small primes
of $b - 1$. For example $x^x equiv x med (mod 3)$ for 5 of every 6 digits
$x >= 1$. So the identity factor $(b - 1) P((b - 1) | F(c) - sigma(c))$ is
large at short lengths. The refined model contains it if it is computed at
the short length itself.

#computation(id: "short-comp-refined-short", title: "Short solutions against the exact refined model", src: "35.1")[
  Expected and observed solutions, summed over the bases $max(9, d)$ to 41:

  #align(center, btable(
    columns: 6,
    align: (right, right, right, right, right, right),
    [$d$], [basic], [refined, $0^0 = 1$], [observed], [refined, $0^0 = 0$], [observed],
    [3], [0.46], [0.72], [1], [0.97], [3],
    [4], [0.39], [0.56], [2], [0.83], [2],
    [5], [0.40], [0.45], [2], [0.61], [4],
    [6], [0.38], [0.47], [1], [0.66], [2],
    [8], [1.13], [1.23], [2], [1.74], [3],
    [12], [1.12], [1.20], [3], [1.79], [2],
  ))

  The short exceptions of @sec-model-window (3 to 5 digits far below the
  base, bases 10 to 41 and 43) have the basic expectation 0.96 and the
  refined expectations 1.35 under $0^0 = 1$ and 1.86 under $0^0 = 0$,
  against 5 and 9 observed.
]

Under $0^0 = 0$ the nine are mostly structured: self-paying zeros, block
pairs and a family member. Under $0^0 = 1$ one of the five is a family
member. The other four are 3435, $(6, 5, 3, 4)$ in base 20,
$(3, 3, 6, 6, 1)$ in base 13 and $(2, 6, 0, 3, 6)$ in base 14. Against
1.35 expected, four or more has probability 0.048, and two of the four are
the 5-digit excess of @short-5-excess.

#heuristic(id: "short-heur-one", title: "One heuristic for every length", src: "35.1")[
  The root heuristic and the per-base refined model are two averages of
  one local density. The root heuristic averages the per-base factors over
  the residue of the base; the refined model keeps the residue of the
  actual base. They agree on totals over many bases. Per base they differ
  by the arrangement factors, which have mean 1 and an RMS of about
  $e^(-0.35 k)$, and by the last-digit factor. The excess of short
  solutions over the basic model has three parts: the identity factor
  modulo $b - 1$ at the short length (1.1 to 2.1 for $x^x$), identity
  families and self-paying blocks, and under $0^0 = 1$ a residual of about
  3 times on four generic strings.
]

The medium lengths test this. For lengths 6 to 12 in bases 7 to 20 the
library computed the root heuristic by sampling, the refined model exactly
(with and without the forced top digit), and the base-by-base calibration
of @short-calibration for lengths 6 to 10.

#computation(id: "short-comp-medium", title: "The two heuristics at 6 to 12 digits", src: "35.2")[
  Bases 7 to 20, all 83 cells of a length from 6 to 12:

  #align(center, btable(
    columns: 5,
    align: (left, right, right, right, right),
    [convention], [observed], [refined], [root, roots mod $p$], [root, roots mod $p^e$],
    [$0^0 = 1$], [10], [8.85], [9.51], [9.74],
    [$0^0 = 0$], [12], [12.72], [13.00], [14.19],
  ))

  Lengths 6 to 10 under $0^0 = 0$, split by the parity of the base:

  #align(center, btable(
    columns: 5,
    align: (left, right, right, right, right),
    [bases], [observed], [calibration], [refined, top digit forced], [root, roots mod $p$],
    [even], [2], [2.38], [2.55], [4.37],
    [odd], [8], [5.77], [5.56], [5.27],
  ))

  Cell by cell the refined model with the top digit forced correlates with
  the calibration at 0.99 under $0^0 = 1$ and 0.94 under $0^0 = 0$.
]

So the two heuristics give the same totals, and both fit the census. Base
by base only the refined model matches the calibration. The root heuristic
averages the parity factor over even and odd bases, as
@short-prop-base-average says it must. The forced top digit matters in
single cells: in base 10 at 6 digits every candidate digit is at most 7,
and one 7 makes $F >= 7^7 = 823 thin 543$, a top digit 8 or 9 that no
candidate contains. No missing factor shows at these lengths, so the
5-digit excess is not a factor that the medium lengths share.

=== What the heuristic cannot see

The completeness of the lists can be estimated with the same heuristic: sum
the expected number of solutions with a digit above the list's bound.

#heuristic(id: "short-tails", title: "Completeness of the lists", src: ("11.4", "19.1"))[
  For strings without an algebraic identity, the expected number of
  solutions missing from the lists is about $10^(-74)$ for 3 digits beyond
  the list with digits up to 80 (and below $10^(-3294)$ beyond
  @short-3digit-range),
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

The heuristic is blind to a second family as well. Under $0^0 = 1$ the
strings $(c^j, 0, dots, 0, x)$ with $x = c^(j c^j) + j - 1$ are solutions
for suitable $c$, because the last digit pays for the weight of $c^j$ and
for the $j - 1$ zeros (@cons-zero-family). For $c = 1$ it is the family
$(1, 0, 0, x)$ seen above at the offset $D = x - 3$. These two linear
families are the only identity families found.

@cons-families-conj states the resulting conjecture: under $0^0 = 1$, all
but finitely many $k$-digit solutions are members of the two linear
families, and every $k$-digit solution beyond the complete lists is one.

The evidence has four parts #lib("25.1"). The complete lists hold no other
solution up to $10^(3301)$ (3 digits), $10^(186)$ (4), $10^(30.9)$ (5) and
$10^(11)$ (6). The root heuristic puts the expected number beyond the lists
at $10^(-74)$ or less. Every power identity $Q_s = lambda A^j - W$ ends in a
large digit, and every identity other than the two linear families needs
one more coincidence, such as a large number being a perfect power. A census
of all small prefixes, up to 7 digits, finds no member of any other
mechanism. The conjecture cannot be strengthened to "finitely many
solutions", since both families are infinite. It fails under $0^0 = 0$,
where the self-paying digits and the swaps give further families. It
replaces the old finiteness conjecture as the answer to question #q(64).

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

The following theorem makes this precise and classifies every 3-digit
string with one large digit.

#theorem(id: "short-three-digit-class", title: "Three digits with one large digit", src: "25.1")[
  Under $0^0 = 1$, let $s = (p, q, r)$ have two digits at most $B >= 1$ and
  a third digit $x >= 2B + 4$, and let $ell$ be the leading digit. Write
  $
    (2 p b + q)^2 = N + R, quad N = 4 ell x^x, quad R = 4 p (F - r) + q^2 - N.
  $
  Then exactly one of the following holds.
  + $R = 0$. Then $x$ is the last digit, $p = lambda c^2$ and
    $q = 2 lambda c e$ with $lambda$ squarefree, $c >= 1$, $e >= 0$, and
    $x = w(p) + w(q) + lambda e^2$. Here $Q_s (r) = lambda (c r + e)^2 - x^x$,
    and $s$ is a solution exactly when $x^x = lambda (c b + e)^2$. For even
    $x$ this needs $lambda = 1$ and $c | x^(x slash 2) - e$, the binomial
    family with $j = 2$. For odd $x$ it needs $x slash lambda$ to be a
    square.
  + $R != 0$ and $N$ is a perfect square. Then $s$ is not a solution.
  + $R != 0$ and $N$ is not a perfect square. Then $Q_s$ has no power
    identity $lambda A^2 - x^x$, and $s$ is a solution exactly when the
    Pell-type equation $U^2 - n V^2 = R$ holds with $U = 2 p b + q$, where
    $N = n V^2$ with $n > 1$ squarefree.
]
#sketch[
  If $x$ leads or sits in the middle, $R$ is a sum of positive terms, so
  $R = 0$ needs $x$ last, with $R = 4p(w(p) + w(q) - x) + q^2$. Then
  $4p | q^2$, and writing $p = lambda c^2$ with $lambda$ squarefree a count
  of prime exponents gives $q = 2 lambda c e$. The equation becomes
  $x^x = lambda (c b + e)^2$. For (ii), let $N = V^2$. If $U > V$ then
  $R >= 2V + 1$, and if $U < V$ then $|R| > V$. So a solution needs
  $|R| > sqrt(N) >= 2 x^(x slash 2)$. But $|R| <= 9 x^2 B^B$ in every
  position, and $x >= 2B + 4$ makes $x^(x slash 2) >= 6 x^2 B^B$. For
  (iii), an identity with one large digit puts it last, and
  $4p(P_s (r) - F(t))$ is a constant times a square exactly when $R = 0$.
]

So among 3-digit strings with one large digit, the identities are exactly
case (i), case (ii) has no solutions, and everything else is the generic
case (iii). The six known 3-digit solutions all have $x <= 7 < 2B + 4$, so
the theorem does not apply to them. $(5, 1, 3)$ in base 25 sits on the
boundary of case (ii): $N = 4 dot 5^6 = 250^2$, $U = 251$ and
$R = 501 = 2 V + 1$.

#remark(id: "short-cor84", src: ("8.2", "22.3", "25.1"))[
  An earlier corollary in the library claimed that the 3-digit solutions
  with two digits at most 20 and the third in its square class are the known
  ones. It assumed $R != 0$, and the binomial members with $R = 0$ refuted
  it: they add $(1, 6, x)$, $(1, 10, x)$, $(1, 14, x)$, $(1, 18, x)$,
  $(4, 8, x)$, $(4, 16, x)$, $(9, 6, x)$ and $(9, 18, x)$, in bases above
  $10^(108942)$. @short-three-digit-class is the final form of that
  corollary.
]

=== Outside the square class

When the dominant term is not a square, we are in case (iii) of
@short-three-digit-class: write $N = n V^2$ with $n$ squarefree. The
equation asks whether $N + R$ is a square: a Pell-type equation
$U^2 - n V^2 = R$ with the extra condition that $V$
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
effective constant 0.5803. Until chapter 32 of the library, no result there
handled equations where the base and the exponent of $x^x$ vary together
#lib("8.2", "9.10"). @sec-short-regimes does it when the quadratic field
stays fixed, with a $p$-adic form of Baker's theorem.

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

== Three regimes for three digits <sec-short-regimes>

@short-three-digit-class turns every 3-digit string with one large digit
$x$ into a Pell-type equation $U^2 - n V^2 = R$, where $n$ is the
squarefree part of $N = 4 ell x^x$. Whether this equation can be handled
for all $x$ at once depends on one thing: how $n$ changes with $x$. The
parity of $x$ decides most of it. If $x$ is even, $x^x = (x^(x slash 2))^2$
is a square. If $x$ is odd, $x^x = x dot (x^((x-1) slash 2))^2$ is $x$ times
a square. So $n$ is the squarefree part of $ell$ (for even $x$ that does not
lead), of $p x$ (for odd $x$ that does not lead, with leading digit $p$), or
of $x$ itself (for even $x$ that leads); for odd $x$ that leads, $N$ is a
square. This gives three regimes and an open remainder #lib("32.1").

#tablefig(caption: [The regimes for 3-digit strings with one large digit $x$ #lib("32.1").], id: "tab-short-regimes")[
  #btable(columns: 4, align: (left, left, left, left),
    [regime], [when], [method], [result],
    [$N$ a square], [$x$ odd and leading; $x$ even behind a square leading digit], [the gap of @short-three-digit-class (ii)], [no solution outside the binomial family],
    [$n$ fixed], [$x$ even, not leading, leading digit not a square], [2-adic Baker (@short-thm-2adic)], [finitely many, explicit bound],
    [$n$ fixed on a class], [$x = lambda t^2$ with $lambda$ fixed: odd and not leading, or even and leading], [real Baker (@short-prop-class)], [finitely many in each class],
    [$n$ varies], [the rest: odd $x$ not leading, even $x$ leading], [none known; abc (@short-abc-three)], [open; finite under abc],
  )
]

The first regime is elementary: two squares cannot be close unless they
are equal. The other two use linear forms in logarithms, explained in
@app-baker.

=== When the field does not change

Fix the digits $p >= 1$ and $q >= 0$, and let $x >= 2$ be even. Consider
the two strings
$ "last:" (p, q, x), quad p b^2 + q b + x = w(p) + w(q) + x^x, $
$ "middle:" (p, x, q), quad p b^2 + x b + q = w(p) + x^x + w(q). $
Write $p = n f^2$ with $n$ squarefree and assume $n > 1$, that is, $p$ is
not a square. Multiply by $4p$ and complete the square. Since $x$ is even,
both equations take the form
$ U^2 - n V^2 = R, quad V = 2 f x^(x slash 2), $
with $U = 2 p b + q$ and $R = q^2 + 4p(w(p) + w(q) - x)$ for the last
position, and $U = 2 p b + x$ and $R = x^2 + 4p(w(p) + w(q) - q)$ for the
middle one. $R$ is not 0, since otherwise $n$ would be a square.

The point is that $n$ does not depend on $x$. All these equations, for
every even $x$, live in one quadratic field $K = QQ(sqrt(n))$, with one
fundamental unit $eta > 1$ (@app-quadratic).

#theorem(id: "short-thm-2adic", title: "A 2-adic bound", src: "32.1")[
  Let $p$ be a positive integer that is not a square, $q >= 0$, and $x$
  even. If $(p, q, x)$ or $(p, x, q)$ is a solution in some base, under
  either convention, then $x <= X_0 (p, q)$, an explicit bound. It comes
  from an inequality whose left side is about $x slash 2$ and whose right
  side grows like $(ln x)^3$.
]
#sketch[
  Put $beta = U - V sqrt(n)$ and $beta' = U + V sqrt(n)$, the two conjugates.
  Then $beta beta' = R$, and $beta' - beta = 2 V sqrt(n)$.

  + The difference is 2-adically tiny. $V = 2 f x^(x slash 2)$ and $x$ is
    even, so $2^(x slash 2 + 1)$ divides $V$ and
    $v(beta' - beta) >= x slash 2 + 2$, where $v$ is the 2-adic valuation,
    extended to $K$ (@sec-app-baker-padic). Since $beta$ divides $R$,
    $v(beta) <= log_2 abs(R)$, and so
    $v(beta' slash beta - 1) >= x slash 2 + 2 - log_2 abs(R)$.
  + Make the height small. $beta'$ is huge, so $beta$ has a large height.
    Multiply by a power of the unit: $delta = beta eta^(-m)$, with $m$ chosen
    so that both conjugates of $delta$ have size about $sqrt(abs(R))$. Then
    $h(delta) <= (1 slash 2) ln(abs(R) eta)$, and $m$ is about
    $ln V slash ln eta$, of order $x ln x$.
  + A 2-adic linear form. Since $eta eta' = plus.minus 1$, the ratio
    $beta' slash beta$ equals $alpha_1 eta^(-2m)$ with
    $alpha_1 = plus.minus delta' slash delta$. So step 1 says that
    $alpha_1 - eta^(2m)$ has 2-adic valuation at least
    $x slash 2 + 2 - log_2 abs(R)$.
  + Bugeaud and Laurent (@app-baker-bl) bound the same valuation from above
    by a constant times $(ln m)^2 ln(abs(R) eta) ln eta$. With $m$ of order
    $x ln x$ and $ln abs(R)$ of order $ln x$, the right side grows like
    $(ln x)^3$, while the left side grows like $x slash 2$. So $x$ is bounded.

  The cases where the theorem of Bugeaud and Laurent does not apply give
  smaller bounds: if $alpha_1$ is not a 2-adic unit, then
  $x slash 2 + 2 <= log_2 abs(R)$; if $alpha_1 = plus.minus 1$, a direct
  computation of $v(eta^(12 m) - 1)$ works; and $m = 0$ forces $x$ to be
  tiny.
]

The argument is the one Bennett and Bugeaud use for approximation by
quadratic irrationals @bennett-bugeaud2012. What is new is that the base
of the power, $x$, moves together with the exponent. That costs nothing:
only the 2-adic valuation of $V$ enters, and the height of $delta$ grows
only like $ln x$.

#computation(id: "short-comp-2adic", title: "No such string with small digits", src: "32.1")[
  For every non-square $p <= 20$, every $q <= 20$ and every even $x$,
  neither $(p, q, x)$ nor $(p, x, q)$ is a solution in any base, under
  either convention. The bounds $X_0 (p, q)$ for the 704 cases (family,
  position, and convention when $q = 0$) reach $2.45 dot 10^9$, for
  $n = 19$, whose unit $170 + 39 sqrt(19)$ is large. A sieve tested all
  $1.98 dot 10^(11)$ values of $x$ below the bounds. The string is a
  solution exactly when $D = U^2$ is a perfect square, and $D$ must then
  be a square modulo each of 150 odd primes. The only values that passed
  every prime are $(3, 1, 2)$, $(3, 2, 2)$ and $(3, 2, 2)$ with $x$ in the
  middle, and their root is $b = 3$, too small for the digit 3.
]

#corollary(id: "short-cor-even", title: "Even large digits", src: "32.1")[
  Let $s$ be a 3-digit solution in some base, under either convention,
  whose leading digit and one other digit are at most 20, and whose third
  digit is even and does not lead. Then $s$ is in the complete lists of
  @sec-short-lists, or it is a member $(c^2, 2 c e, x)$ of the binomial
  family (@thm-binomial with $j = 2$).
]
#proof[
  If the leading digit is not a square, use @short-comp-2adic. If it is a
  square and $x < 44$, then $p b^2 <= F < 2 dot 20^20 + 42^42$, so
  $b < 2 dot 10^(34)$, inside the lists. If $x >= 44 = 2 dot 20 + 4$,
  @short-three-digit-class applies with $B = 20$: $N = 4 p x^x$ is a
  square, so case (iii) is empty, case (ii) has no solution, and case (i)
  is the family. That theorem is stated under $0^0 = 1$, but for $x$ in the
  middle or last position its proof works under $0^0 = 0$ as well.
]

Of the known 3-digit solutions only $(1, 2, 6)$ in base 215 has this shape,
and it is the first member of the family.

The bound can be made uniform in the small digits. If $p, q <= B$, the
regulator $ln eta$ is at most $sqrt(B)(ln 4B + 2)$ by the class number
formula, and the same inequality gives $x <= C B^(3 slash 2) (ln 3B)^4$ for
an effective constant $C$ (Theorem 32.5 of #lib("32.1")). So the large
digit of such a solution cannot be much larger than the small ones, unless
the solution is a family member.

These families have no known covering (@sec-short-coverings). Each odd
prime $l$ leaves about $(l + 1) slash (2 l)$ of the residues of $x$, and
the first five primes leave about 7% of the even $x$. Every single member
fails modulo some prime, but a finite set of primes has a fixed period,
while $x$ is unbounded. The bound from transcendence theory replaces the
covering, and a finite sieve does the rest.

=== A fixed square class

When $x$ is odd and does not lead, $n$ is the squarefree part of $p x$, so
the field changes with $x$. It stays fixed if $x$ runs through one square
class $x = lambda t^2$ with $lambda$ fixed. The same holds for an even $x$
that leads.

#proposition(id: "short-prop-class", title: "One square class", src: "32.1")[
  Fix $p$, $q$, the position of $x$ and a squarefree $lambda$. Then only
  finitely many $x$ with squarefree part $lambda$ make the string a
  solution, and their number is effectively bounded.
]
#sketch[
  The field is fixed, $V$ is a constant times a power of $t$ and $lambda$,
  and the associate $delta$ of the previous proof has height $O(ln x)$. Now
  the real absolute value does the work: the real linear form
  $ln(2 sqrt(n) V) - ln delta - m ln eta$ is at most about
  $abs(R) slash V^2$, roughly $x^(-x)$. It has four logarithms, and
  Matveev's theorem (@app-baker-matveev) bounds it below by
  $exp(-c (ln x)^3)$. For large $x$ this contradicts $x^(-x)$. There is no
  2-adic shortcut here, because $V$ is odd.
]

#computation(id: "short-comp-oddsq", title: "Odd squares", src: "32.1")[
  For every non-square $p <= 20$, every $q <= 20$ and every odd $t >= 3$,
  neither $(p, q, t^2)$ nor $(p, t^2, q)$ is a solution in any base, under
  either convention. Matveev's bound gives $t <= 3.94 dot 10^9$ in these
  cases, and the sieve tested all $6.07 dot 10^(11)$ values of $t$. The
  only survivors have $t = 1$; among them are the solutions $(p, 0, 1)$ in
  base $p^((p - 1) slash 2)$ for odd non-square $p$, with $0^0 = 0$. So
  @short-cor-even holds for digits at most 20 with "even" replaced by
  "even or an odd square".
]

=== Where the frontier is

What is left of the 3-digit problem with one large digit is the last row
of @tab-short-regimes: Pell equations in which the field $QQ(sqrt(p x))$ or
$QQ(sqrt(x))$ changes with $x$. The regulator of such a field can be as
large as $sqrt(x) ln x$, and then every known form of Baker's theorem is too
weak by a power of $ln x$. A treatment of a whole family of real quadratic
fields at once, for example through results on $y^2 = a x^n + c$ that are
uniform in $n$, would settle the case up to a finite computation (#q(129),
#q(130)).

The abc conjecture (@app-abc) closes every regime at once, in the
completed-square form #lib("33.4"). In $U^2 = N + R$ the radical of the
three terms is at most about $abs(R) dot 4 ell x dot U$, about
$x^(x slash 2 + 3) B^B$, while $U^2$ is about $x^x$. The quality tends
to 2. Written as $x^x = p b^2 + q b + (x - C)$ instead, the radical contains
$b$, about $x^(x slash 2)$, and abc says nothing. The completed square is
what makes it work.

#theorem(id: "short-abc-three", title: "Three digits under abc", status: "conditional", src: "33.4")[
  Assume the abc conjecture. For every $epsilon > 0$ there is a constant
  $C_epsilon$ with the following property. Let $s$ be a 3-digit string,
  under either convention, with two digits at most $B$ and a third digit
  $x >= 2B + 4$, in any position and of any parity, and write
  $U^2 = N + R$ as in @short-three-digit-class. If $R != 0$ and $s$ is a
  solution, then $x <= (2 + epsilon) B + C_epsilon$. The same holds for
  factorions.
]
#sketch[
  Let $g = gcd(N, R)$. If $R > 0$, the triple $N slash g + R slash g = U^2 slash g$
  is coprime; if $R < 0$, use $U^2 slash g + abs(R) slash g = N slash g$.
  Its radical is at most $"rad"(N) dot U dot abs(R) slash g$, and
  $"rad"(N) <= 2 ell x$. abc gives
  $N <= K_epsilon ("rad"(N) U abs(R))^(1 + epsilon)$. Since
  $abs(R) < sqrt(N)$, $U^2 <= 2 N$. With $ln N >= x ln x$ and
  $abs(R) <= 9 x^2 B^B$ this becomes
  $x ln x <= (2 + O(epsilon)) (B ln B + 5 ln x) + O_epsilon (1)$, so
  $x <= (2 + O(epsilon)) B + C_epsilon$. For factorials the radical of
  $N$ is about $e^x$ instead, and the same steps give a bound.
]

So under abc every 3-digit solution with one dominant digit, a digit larger
than about twice the others, is a member of the binomial family, case (i)
of @short-three-digit-class. Up to finitely many exceptions this proves
@cons-families-conj for 3 digits in that range. With an explicit form of
abc the constant is explicit (@sec-app-abc-explicit).

#tablefig(caption: [The largest $x$ that the explicit form $c < "rad"(a b c)^(7 slash 4)$ allows when the other two digits are at most $B$ and $R != 0$ #lib("33.4").], id: "tab-short-abc")[
  #btable(columns: 7, align: (left, right, right, right, right, right, right),
    [$B$], [1], [10], [100], [200], [500], [1000],
    [$x^x$, last], [37], [105], [974], [1,991], [5,130], [10,484],
    [$x^x$, middle], [45], [105], [974], [1,991], [5,130], [10,484],
    [$x^x$, leading], [38], [105], [970], [1,986], [5,124], [10,478],
    [$x!$, all], [$4.10 dot 10^6$], [$4.10 dot 10^6$], [$4.11 dot 10^6$], [$4.12 dot 10^6$], [], [$4.19 dot 10^6$],
  )
]

For $x^x$ the ratio $x slash B$ is about 10 in this range and tends to 14
slowly. For $x!$ the bound hardly depends on $B$: the radical of $x!$ is
about $e^x$, so abc beats $x!$ only once $ln x$ exceeds about 15.

#corollary(id: "short-abc-explicit", title: "The 3-digit list under the explicit abc", status: "conditional", src: "33.4")[
  Assume $c < "rad"(a b c)^(7 slash 4)$ for all coprime $a + b = c$. Then
  every 3-digit solution under $0^0 = 1$ with two digits at most 200 is one
  of the six known ones or a binomial member, case (i) of
  @short-three-digit-class.
]
#proof[
  By @tab-short-abc, $x <= 1991$ when $R != 0$. Part 1 of
  @short-3digit-range decided every string with digits up to 2000.
]

This removes the restriction to bases below $46666^(23333) - 3$ from
part 2 of @short-3digit-range, at the price of the hypothesis. What abc leaves is two large digits $u >= v$. Moving the
second large term into $R$ and applying abc again leaves only
$v ln v >= (1 slash 2 - epsilon) u ln u$, about $v >= u slash 2$ (with
the exponent $7 slash 4$, about $v >= u slash 14$). In that range the
equation $U^2 = 4 ell (u^u + v^v) + R$ has four large terms. abc does not
apply to four terms, its $n$-term generalization @browkin-brzezinski1994
is too weak here, and $u^u + v^v$ is not a perfect power, so Fermat-Catalan
statements do not apply either (#q(136)).

For four or more digits the method needs the polynomial to be a perfect
power up to a small remainder in a fixed field. That happens only for
special prefixes, for example $q^2 = 3 p r$ for $(p, q, r, x)$, which
gives a Thue equation in $QQ(p^(1 slash 3))$ (#q(131)). Otherwise the
equation defines a curve of genus at least 1 that changes with $x$.

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
The digit-sum identity repairs this: $b - 1$ divides $F(c) - sigma(c)$, where
$sigma(c)$ is the digit sum of $c$ (@thm-digit-sum).

#lemma(id: "short-divisors", title: "Divisors in a short interval", src: "20.1")[
  Let $d_1 < dots < d_r$, with $r >= 1$, be divisors of $m >= 1$ in an interval $(Y - h, Y]$
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
$F(c) - sigma(c) = sum (d^d - d)$ spread evenly over residue classes modulo the
integers $b - 1$ of a short window that depends on $F(c)$ itself. No method
for this is known #lib("20.1").

Question #q(101) asked whether averaging over the bases gets around this.
Split a multiset into large digits and small digits, whose weights add up
to less than $b - 1$. Given the large part and the base, the congruence
$(b - 1) | F(c) - sigma(c)$ fixes the small part of $F(c) - sigma(c)$
exactly, and dissociation (@sec-model-anticonc) bounds the number of small
multisets with a given value. The count becomes a sum over the large parts
and the bases of their windows. The gain is bounded, because most
multisets have no small digit at all.

#proposition(id: "short-prop-no-small", title: "Averaging gains a bounded factor", src: "35.4")[
  Let $K = kappa L slash ln L$ with $kappa$ bounded, $X = X_K (B)$, and let
  $z$ be the largest digit with $z^z <= B^A$ for a fixed $A > 0$. Among the
  multisets of $K$ digits from $0, dots, X$, the share with no digit up to
  $z$ is $e^(-2A + o(1))$. So the averaged count, with the window factor of
  @short-multiset-count, is at least $e^(-2A - o(1))$ times the bound of
  @short-multiset-count. Small weights stay below $b <= B$, so $A < 1$, and
  averaging in this form gains at most a factor $e^(2 + o(1))$.
]
#sketch[
  The share is $product_(i = 1)^K (1 - (z + 1) slash (X + i))$. From
  $X ln X approx K L$ and $z ln z approx A L$ one gets
  $K z slash X -> 2A$. A multiset without small digits enters the averaged
  count exactly as in @short-multiset-count. The term $k = K$ carries
  almost all of the sum over $k <= K$ #lib("35.4").
]

#computation(id: "short-comp-averaged", title: [The averaged bound at $B = 10^96$], src: "35.4")[
  With $z = 30$, the averaged bound is $B^(0.9698)$ at $K = 48$ against
  $B^(0.9725)$ for @short-multiset-count, a factor 1.8. Both stay below $B$
  up to $K = 49$, and up to $K = 362$ at $B = 10^1000$.
]

The window does not see the small digits at all. That gives a range far
beyond $ln b slash ln ln b$ for strings with few large digits.

#theorem(id: "short-thm-few-large", title: "Few large digits", src: "35.4")[
  Fix $C >= 1$ and $epsilon > 0$. Call a digit $x$ large when
  $x^x >= sqrt(b)$. Almost all bases $b$ have no solution of length at most
  $(ln b)^C$ with at most $(1 slash C - epsilon) ln b slash ln ln b$ large
  digits, whatever the number of smaller digits. Up to $B$, at most
  $B^(max(1 slash 2, 1 - C epsilon) + o(1))$ bases have one.
]
#sketch[
  The small digits weigh less than $k sqrt(b)$ in all. That moves
  $(F slash p)^(1 slash (k - 1))$ by less than 1, so the base lies in a
  window fixed by the large digits, the length and the leading digit. Count
  these data: the large part is one of
  $binom(X + K', K')$ multisets with $K' = (1 slash C - epsilon) L slash ln L$
  and $ln X <= (C + 1) ln L$, so its logarithm is at most
  $(1 - C epsilon) L (1 + o(1))$. The other factors are $exp(O(ln L))$
  #lib("35.4").
]

For $C = 1$ this reaches lengths up to $ln b$. Typical strings of that
length have almost all digits large, so the theorem says nothing about
them. It covers the structured strings: a few large digits padded with
small ones, the shape of the self-paying and binomial families
(@sec-cons-binomial). Those families live in sparse sets of bases, which
agrees with the theorem.

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
  Under $0^0 = 1$, base 25 is the only base below $10^(3301)$ with both a
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

=== How many 3-digit solutions can one base have?

Base 4 has two 3-digit solutions, $(1, 3, 1)$ and $(3, 1, 3)$.

#computation(id: "short-at-most-two", title: "At most two", src: "25.3")[
  Under $0^0 = 1$, every base up to $10^(3301)$ has at most two 3-digit
  solutions, and base 4 is the only one with two.
]

Can a proof reach all bases? The first step is that the largest digit is
almost fixed by the base.

#lemma(id: "short-largest-digit", title: "The largest digit", src: "25.3")[
  Let $s$ be a 3-digit solution in base $b$ with leading digit $p$ and
  largest digit $M$. Then $b^2 slash 3 <= w(M) < (M + 1) b^2$ and
  $p = floor(F slash b^2)$.
]
#proof[
  $F = p b^2 + q b + r$ with $q b + r < b^2$, so $p = floor(F slash b^2)$
  and $b^2 <= F < (p + 1) b^2$. Each weight is at most $w(M)$, so
  $F <= 3 w(M)$, and $w(M) <= F < (p + 1) b^2 <= (M + 1) b^2$.
]

#corollary(id: "short-two-values", title: "Two consecutive values", src: "25.3")[
  The largest digits of the 3-digit solutions of one base take at most two
  values, and these are consecutive.
]
#proof[
  If $M_1 <= M_2 - 2$ both occur, @short-largest-digit gives
  $w(M_2) < 3 (M_2 + 1) w(M_1) <= 3(M_2 + 1) w(M_2 - 2)$. But
  $w(M_2) slash w(M_2 - 2) >= 3 M_2^2$.
]

#theorem(id: "short-thirty", title: "At most 30 per base", src: "25.3")[
  Let $b >= 5$. Under $0^0 = 1$, base $b$ has at most 30 three-digit
  solutions, unless $|b - M^((M-1) slash 2)| <= 6$ for a value $M$ with
  $b^2 slash 3 <= w(M) < (M + 1) b^2$. Then it has at most $2M + 24$. There
  are at most 13 such exceptional bases for each $M$.
]
#sketch[
  Fix one of the at most two values $M$, and let $u, v$ be digits below $M$.
  @tab-short-shapes counts the solutions of each shape: in each, the
  equation fixes the value of an injective function of one digit, or of a
  function that takes each value at most twice. For the shapes whose
  leading digit is below $M$, $F slash b^2$ lies in an interval of length
  below 1, so the leading digit takes at most two values. This leaves the
  shape $(M, u, v)$, with the equation $w(u) + w(v) - u b - v = M b^2 - w(M)$.
  Two of its solutions must share their digits above the largest $T$ with
  $w(T) <= 2M(b + 1)$, since a larger differing digit changes the weight sum
  by more than $M(b + 1)$. With two or one digits above $T$ there are at
  most 1 or 3 solutions. With none, $|b^2 - M^(M-1)| <= 5(b + 1)$, so $b$
  is within 6 of $M^((M-1) slash 2)$, and there are at most $M$ solutions.
]

#tablefig(caption: [The shapes of 3-digit solutions with largest digit $M$
  in one base, with $u, v < M$ #lib("25.3").], id: "tab-short-shapes")[
  #btable(
    columns: 3,
    align: (left, left, right),
    [shape], [equation], [solutions],
    [$(M, M, M)$], [one equation in $b$], [at most 1],
    [$(M, M, u)$], [$g(u) = M b^2 + M b - 2 w(M)$], [at most 1],
    [$(M, u, M)$], [$u b - w(u) = 2 w(M) - M - M b^2$], [at most 2],
    [$(u, M, M)$], [$u b^2 - w(u) = 2 w(M) - M b - M$], [at most 2],
    [$(u, M, v)$], [$u$ takes 2 values, then $g(v)$ is fixed], [at most 2],
    [$(u, v, M)$], [$u$ takes 2 values, then $v b - w(v)$ is fixed], [at most 4],
    [$(M, u, v)$], [$w(u) + w(v) - u b - v = M b^2 - w(M)$], [at most 3, or $M$],
  )
]

This is a constant bound outside at most about $26 ln X slash ln ln X$
bases up to $X$, against the power of $log b$ of @short-per-base. It does
not reach 2. The weak point is the shape $(M, u, v)$, where each solution
is an exact coincidence. In the bases of the binomial families more is
known.

#proposition(id: "short-one-member", title: "One member per base", src: "25.3")[
  A base has at most one 3-digit member of the binomial families.
]

#proposition(id: "short-member-base", title: "Bases with a member", src: "25.3")[
  Let $(p, q, x)$ be a member in base $b$, with $x = w(p) + w(q) + lambda e^2$.
  Every other 3-digit solution of base $b$ is $(p, x, r)$ with
  $w(r) - r = (x - q) b - w(p) - lambda e^2$, or $(p, q', x)$ with $q' != q$
  and $w(q') - w(q) = (q' - q) b$. Each equation has at most one solution,
  so base $b$ has at most 3 three-digit solutions.
]

For each of the 80 members with $x < 10^(300)$, among them base
$46666^(23333) - 3$, the candidates for the two equations fail modulo some
prime, so the member is the only 3-digit solution of its base
#lib("25.3").

#problem(id: "short-q50", title: "At most two 3-digit solutions", src: ("18.2", "25.3"))[
  Under $0^0 = 1$, does every base have at most two 3-digit solutions?
  (Question #q(50).) It holds for every base up to $10^(3301)$
  (@short-at-most-two), and every base has at most 30 outside a sparse set
  (@short-thirty). A third solution needs three independent coincidences,
  so "at most two" is expected for every base. A proof needs control of the
  shape $(M, u, v)$, where a base near $M^((M-1) slash 2)$ gives one
  equation in two free digits.
]
