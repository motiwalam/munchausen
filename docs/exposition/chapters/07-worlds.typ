#import "../template.typ": *

= Other number systems and other weights <ch-worlds>

The definition of a Munchausen number has two ingredients: a way to write
numbers with digits, and a weight for each digit. Chapters 1 to 6 keep both
fixed: an integer base $b >= 2$ and the weight $x^x$. This chapter changes
them. It writes numbers in negative, imaginary, Gaussian, Eisenstein,
rational and Pisot bases, in the polynomial ring $FF_q [T]$ and in the
factorial number system, and it replaces $x^x$ by $x^(x+t)$, by $x!$ and by
$x^d$.

The aim is to sort the facts of the earlier chapters into two kinds. Some
hold in every world where the probabilistic model of @ch-model makes sense:
about one solution per base and convention, a Poisson count, and a factor 2
whenever a certain modulus is even. Others belong to $x^x$ and the integers:
the length shares 8, 55 and 23 percent, the twins, the self-paying digits.
Two worlds break the model outright, and they show why it works elsewhere.
@sec-worlds-ffield on function fields is the clearest case in this document
of a coincidence model that fails, and of the exact reason.

== A common frame <sec-worlds-frame>

Every world in this chapter has a set of digits, a rule that gives each
number exactly one digit string, and a weight $w(d)$ for each digit, with
$w(0) = m$ for the convention $0^0 = m$. A solution is a number $n$ with at
least two digits and $n = F(n)$, where $F(n)$ is the sum of the weights of
its digits.

The model of @sec-model-basic carries over almost word for word. Split the
numbers into windows $W$, for example the numbers with exactly $k$ digits.
Pretend that the sum $F$ of a random string from $W$ is a random number of
its window.

#heuristic(id: "worlds-basic-model", title: "The windows model", src: ("5.1", "21"))[
  The expected number of solutions is
  $ E = sum_W P(F(N) in W), quad N "uniform in" W. $
  Each term is the chance that the sum of a random string of the window
  lands in the same window. In every world where the length of $F(N)$ barely
  depends on the length of $N$, these chances add up to about 1.
]

The second ingredient is an identity that every number obeys. In base $b$
every integer is congruent to its digit sum modulo $b - 1$
(@thm-digit-sum). Most worlds have such a modulus.

#definition(id: "worlds-def-modulus", title: "Identity modulus", src: "21")[
  An _identity modulus_ of a number system is an integer $M >= 2$ such that
  every number is congruent to its digit sum modulo $M$. A solution then
  satisfies $sum_d (w(d) - d) equiv 0 med (mod M)$, the sum over its digits.
]

The refined model of @sec-model-refined draws the sum at random among the
numbers that obey this identity. A digit multiset that meets the condition
becomes $M$ times as likely, and the others become impossible. On average
nothing changes, unless the condition holds more often than $1 slash M$ of
the time. It does so in one situation.

#heuristic(id: "worlds-free-factor", title: "Free residue factor", src: ("5.3", "14.6", "21"))[
  If $M$ is even and $w(d) equiv d med (mod 2)$ for every digit $d >= 1$,
  then under $0^0 = 0$ the identity holds modulo 2 for free, and the
  expected number of solutions doubles. Under $0^0 = 1$ each zero adds 1, so
  the factor applies only to strings with an even number of zeros, and it
  is $1 + e^(-2) approx 1.135$ when the number of zeros is a Poisson count
  with mean 1, as in a long string. When zeros are rare it tends to 2.
]

For $x^x$ the condition $w(d) equiv d med (mod 2)$ always holds, since
$x^x$ and $x$ have the same parity. So the question in each world is whether
its identity modulus is even. The function field $FF_q [T]$ has a stronger
version of the same mechanism: there the weights agree with the digits at
every prime factor of the modulus (@sec-worlds-ffield).

Two kinds of structure sit outside the model, as in the integers. _Twins_
are pairs of solutions that differ in the last digit (@thm-twins).
_Self-paying digits_ are digits whose weight equals their value at some
position (@thm-self-paying). Both come from exact identities, not from
chance.

The last tool is the near-solution count of @sec-model-defects. For an
offset $D$ in the residue class of 0 modulo the identity modulus, count the
$n$ with $n = F(n) + D$. Each such offset is another draw of the same
coincidence with the true weights. The mean count per offset measures the
real rate of solutions without any model. In this chapter "near" always
means this mean.

@worlds-tab-systems lists the worlds of this chapter.

#tablefig(caption: [The number systems of this chapter.], id: "worlds-tab-systems")[
  #btable(
    columns: 4,
    align: (left, left, left, left),
    [system], [digits], [identity modulus], [section],
    [base $b >= 2$], [$0, dots, b - 1$], [$b - 1$], [@sec-model-refined],
    [base $-b$], [$0, dots, b - 1$], [$b + 1$], [@sec-worlds-negative],
    [base $c i$], [$0, dots, c^2 - 1$], [reduces to $-c^2$], [@sec-worlds-complex],
    [Gaussian base $-n + i$], [$0, dots, n^2$], [$(n+1)^2 + 1$], [@sec-worlds-complex],
    [Eisenstein base $-n + omega$], [$0, dots, n^2 + n$], [$n^2 + 3n + 3$], [@sec-worlds-complex],
    [rational base $p slash q$], [$0, dots, p - 1$], [$p - q$], [@sec-worlds-rational],
    [Pisot base $epsilon_x$], [$0, dots, x$], [$x$], [@sec-worlds-pisot],
    [$FF_q [T]$, base $B$ of degree $e$], [polynomials of degree $< e$], [$B - 1$], [@sec-worlds-ffield],
    [factorial system], [$0 <= d_i <= i$], [none], [@sec-worlds-factorial],
  )
]

Appendix @app-numeration explains how each of these number systems works
and why its representations are unique.

== Negative bases <sec-worlds-negative>

=== Representations and first examples

In base $-b$, with $b >= 2$, every integer has exactly one representation
$n = sum_i s_i (-b)^i$ with digits $0 <= s_i <= b - 1$ and no sign
(@app-numeration). A string $s$ is a Munchausen number in base $-b$ when
$n = F(n)$, with the same weights as before. In the language of
@sec-basics-polynomial, these are the integer roots of the Munchausen
polynomial $Q_s$ at negative arguments $r < -max(s)$.

#proposition(id: "worlds-odd-length", title: "Odd length", src: "12.3")[
  A Munchausen number in a negative base has an odd number of digits.
]
#proof[
  Its value $F(s)$ is positive. A string of length $k$ in base $-b$ with a
  nonzero leading digit has the sign of $(-b)^(k-1)$, because the leading
  term outweighs all the others. So $k - 1$ is even.
]

#example(id: "worlds-ex-404201091", src: "12.3")[
  In base $-10$ the number $404201091$ has the digits
  $(4, 0, 5, 8, 1, 9, 1, 1, 1)$. Indeed
  $4 dot 10^8 + 5 dot 10^6 - 8 dot 10^5 + 10^4 - 9 dot 10^3 + 100 - 10 + 1 = 404201091$,
  and under $0^0 = 1$
  $ 4^4 + 1 + 5^5 + 8^8 + 1 + 9^9 + 1 + 1 + 1 = 404201091. $
  A smaller example is $(1, 3, 4, 3, 3)$ in base $-5$:
  $625 - 375 + 100 - 15 + 3 = 338 = 1 + 27 + 256 + 27 + 27$.
]

The structure of the integer case carries over with $b + 1$ in place of
$b - 1$. The key fact is that prefixes still give intervals.

#proposition(id: "worlds-prefix-intervals", title: "Prefix intervals", src: "14.1")[
  Let $max_j = (b-1)(1 + b^2 + b^4 + dots)$ and
  $"negmin"_j = (b-1)(b + b^3 + dots)$, the sums over the even and the odd
  positions below $j$. The integers with at most $j$ digits in base $-b$
  are exactly the integers in $[-"negmin"_j, max_j]$. The integers whose
  digits at positions $>= j$ are fixed form a translate of this interval by
  a multiple of $b^j$.
]
#proof[
  The $b^j$ strings of length $j$ have distinct values, and all lie in the
  interval. The interval has
  $max_j + "negmin"_j + 1 = (b - 1)(1 + b + dots + b^(j-1)) + 1 = b^j$
  integers, so the strings fill it. Fixing the top part to a value $u$ gives
  the set $u (-b)^j + [-"negmin"_j, max_j]$.
]

So for odd $d$ the integers with exactly $d$ digits form the interval
$(b^(d-1) - 1) slash (b+1) < n <= (b^(d+1) - 1) slash (b+1)$, a window
twice as wide in digits as in a positive base. The integers with an even
number of digits are all negative. A second fact makes base $-b$ arithmetic
as cheap as base $b$ arithmetic: $n + "negmin"_d$ has the base-$b$ digits
$s_i$ at even positions and $b - 1 - s_i$ at odd positions (#lib("14.1"),
Proposition 14.3). The search engine of @sec-search-tree therefore runs
unchanged on shifted digit vectors, and it grows about $1.9$ times per base,
as in positive bases (#lib("14.2")).

=== The identity modulus is b + 1

#proposition(id: "worlds-nega-residue", title: "The only invariant residue", src: "14.1")[
  Let $M >= 2$. The residue $n mod M$ depends only on the digit multiset of
  $n$, for all $n$ with at least 3 digits in base $-b$, exactly when $M$
  divides $b + 1$. Every solution satisfies
  $sum_x (w(x) - x) equiv 0 med (mod b + 1)$.
]
#proof[
  Since $-b equiv 1 med (mod b + 1)$, every $n$ is congruent to its digit
  sum modulo $b + 1$. Conversely, swap the last two digits $x$ and $y$ of a
  number with at least 3 digits, with $x - y = 1$. The leading digit does
  not move, the multiset stays the same, and the value changes by
  $(x - y)(-b) + (y - x) = -(b + 1)$. So $M$ divides $b + 1$. For a
  solution, $n = F(n)$ gives the identity.
]

The consequences of @sec-basics-congruences move with the modulus. For odd
$b$ and $0^0 = 1$, a solution has an even number of zeros; for odd $b$ and
$0^0 = 0$ the identity holds modulo 2 for free. So the parity doubling of
@worlds-free-factor happens in base $-b$ for odd $b$, where $b + 1$ is even.
Both $b - 1$ and $b + 1$ are even exactly when $b$ is odd, so the same
$|b|$ doubles in both signs.

#proposition(id: "worlds-nega-length", title: "Length", src: "14.1")[
  A solution in base $-b$ has an odd number $k <= b + 1$ of digits. So
  $k <= b + 1$ for even $b$ and $k <= b$ for odd $b$.
]
#sketch[
  Odd length is @worlds-odd-length. For odd $k >= b + 2$,
  $F(n) <= k (b-1)^(b-1)$ while $n > (b^(k-1) - 1) slash (b + 1)$, and a
  direct estimate shows $k (b+1)(b-1)^(b-1) + 1 <= b^(k-1)$ for all such
  $k$. The factor $(1 - 1 slash b)^(b-1) <= 0.422$ for $b >= 4$ does the
  work; bases 2 and 3 are checked by hand (#lib("14.1")).
]

The bound is reached: base $-10$ has the 11-digit solution
$(1, 9, 2, 1, 7, 4, 5, 8, 9, 8, 9)$ and base $-14$ a 15-digit one.

=== The length law

The large-base analysis of @sec-model-basic adapts. The largest digit
present fixes the size of $F$, and the windows of lengths now sit at even
powers of $b$ apart.

#heuristic(id: "worlds-nega-shares", title: "Length shares in negative bases", src: "14.1")[
  In the large-base limit a negative base has about one solution per
  convention before the identity factor, with these shares by length:

  #align(center, btable(
    columns: 4,
    align: (left, right, left, right),
    [even $b$], [share], [odd $b$], [share],
    [$b + 1$ digits (3 or more copies of $b - 1$)], [8.0%], [$b$ digits (at least one $b - 1$)], [63.2%],
    [$b - 1$ digits], [78.4%], [$b - 2$ digits], [31.8%],
    [$b - 3$ digits], [11.7%], [$b - 4$ digits], [4.3%],
    [$b - 5$ digits], [1.6%], [$b - 6$ digits], [0.6%],
    [fewer], [0.3%], [fewer], [0.1%],
  ))

  The refined factors are 1 and 2 under $0^0 = 0$, and 1 and
  $1 + e^(-2)$ under $0^0 = 1$, for even and odd $b$.
]

For example, for even $b$ and $k = b + 1$ the window starts near
$b^(b-1)$, and $c$ copies of $b - 1$ give $F approx (c slash e) b^(b-1)$. So
$F$ lands in the window when $c >= 3$, with probability
$1 - (5 slash 2) e^(-1) approx 0.080$, the same 8% as for $b$-digit
solutions in positive bases.

=== The census

#computation(id: "worlds-nega-census", title: [Negative bases $-2$ to $-38$], src: ("12.3", "14.3", "23.2"))[
  @worlds-tab-negacensus lists the number of solutions and their lengths
  in every base from $-2$ to $-38$, under both conventions. The search is
  exhaustive in each base.
]

#tablefig(caption: [Solutions in negative bases. "lengths" lists the length of each solution. $E_m$ is the refined model. Data: #lib("14.3", "23.2"), `data/negative-bases.csv`.], id: "worlds-tab-negacensus")[
  #btable(
    columns: 7, size: 8pt,
    align: (right, right, left, right, right, left, right),
    [base], [$0^0 = 1$], [lengths], [$E_1$], [$0^0 = 0$], [lengths], [$E_0$],
    [$-2$], [1], [3], [0.75], [2], [3, 3], [2.25],
    [$-3$], [0], [], [1.11], [0], [], [1.33],
    [$-4$], [0], [], [1.05], [1], [5], [0.63],
    [$-5$], [1], [5], [1.16], [2], [3, 5], [2.54],
    [$-6$], [0], [], [1.20], [0], [], [1.17],
    [$-7$], [3], [3, 7, 7], [1.48], [4], [3, 3, 7, 7], [2.55],
    [$-8$], [1], [7], [1.36], [2], [3, 3], [1.58],
    [$-9$], [0], [], [1.40], [0], [], [2.31],
    [$-10$], [3], [9, 9, 11], [1.30], [4], [9, 9, 9, 11], [1.24],
    [$-11$], [2], [9, 11], [1.61], [2], [11, 11], [2.80],
    [$-12$], [1], [11], [1.23], [0], [], [1.27],
    [$-13$], [1], [13], [1.44], [4], [7, 13, 13, 13], [2.48],
    [$-14$], [2], [13, 15], [1.20], [1], [15], [1.12],
    [$-15$], [0], [], [1.38], [0], [], [2.37],
    [$-16$], [0], [], [1.18], [1], [15], [1.13],
    [$-17$], [1], [17], [1.34], [2], [17, 17], [2.29],
    [$-18$], [0], [], [1.12], [0], [], [1.12],
    [$-19$], [1], [19], [1.30], [1], [19], [2.27],
    [$-20$], [0], [], [1.12], [0], [], [1.12],
    [$-21$], [2], [21, 21], [1.31], [1], [21], [2.25],
    [$-22$], [0], [], [1.11], [1], [21], [1.11],
    [$-23$], [1], [23], [1.30], [2], [21, 23], [2.27],
    [$-24$], [0], [], [1.10], [3], [23, 23, 23], [1.09],
    [$-25$], [0], [], [1.27], [2], [3, 3], [2.18],
    [$-26$], [1], [27], [1.08], [0], [], [1.07],
    [$-27$], [1], [25], [1.24], [2], [25, 27], [2.15],
    [$-28$], [2], [23, 27], [1.06], [1], [23], [1.05],
    [$-29$], [0], [], [1.21], [1], [27], [2.13],
    [$-30$], [0], [], [1.05], [0], [], [1.05],
    [$-31$], [4], [31, 31, 31, 31], [1.19], [5], [29, 29, 31, 31, 31], [2.10],
    [$-32$], [2], [31, 31], [1.05], [4], [13, 13, 31, 31], [1.06],
    [$-33$], [1], [33], [1.21], [3], [33, 33, 33], [2.09],
    [$-34$], [0], [], [1.05], [0], [], [1.04],
    [$-35$], [0], [], [1.23], [1], [33], [2.14],
    [$-36$], [3], [33, 35, 35], [1.06], [1], [35], [1.06],
    [$-37$], [1], [37], [1.18], [1], [37], [2.08],
    [$-38$], [0], [], [1.04], [0], [], [1.04],
  )
]

The small bases show the same algebraic structure as positive bases.
Under $0^0 = 0$ twins appear in bases $-2$, $-7$, $-8$, $-10$, $-25$ and
$-32$. For $x$ odd or a square, $(x, 0, 0)$ and $(x, 0, 1)$ are solutions in base
$-x^((x-1) slash 2)$ as well as in base $x^((x-1) slash 2)$, which gives
$(4, 0, 0)$ in base $-8$ and $(5, 0, 0)$ in base $-25$. In base $-32$ the
digit 16 pays for itself at position 12, because
$16 dot 32^12 = 2^64 = 16^16$ and $(-32)^12 > 0$. The solutions with $b + 1$
digits, in bases $-10$, $-14$ and $-26$, all start with the digit 1
followed by $b - 1$, as the length analysis predicts.

#proposition(id: "worlds-partner-conventions", title: "Partners between the conventions", src: "23.2")[
  If $n$ is a solution under $0^0 = 0$ that ends in the digit 2 and has
  exactly two zero digits, then $n - 1$ is a solution under $0^0 = 1$. This
  holds in every base $b$ and $-b$.
]
#proof[
  The number $n - 1$ ends in 1 and has the same other digits. So
  $F_1(n - 1) = F_0(n) + 2 - w(2) + w(1) = n + 2 - 4 + 1 = n - 1$, where the
  2 counts the two zeros under $0^0 = 1$.
]

Base $-36$ shows it: a 35-digit string ending in $(dots, 7, 2)$ under
$0^0 = 0$ and the same string ending in $(dots, 7, 1)$ under $0^0 = 1$.

=== Counts against the model

#computation(id: "worlds-nega-vs-model", title: "Counts against the model", src: "14.3")[
  Over bases $-10$ to $-35$:

  #align(center, btable(
    columns: 5,
    align: (left, left, right, right, right),
    [convention], [bases], [observed], [refined model], [basic model],
    [$0^0 = 0$], [even $b$], [15], [14.5], [14.6],
    [$0^0 = 0$], [odd $b$], [26], [29.5], [14.5],
    [$0^0 = 1$], [even $b$], [11], [14.6], [14.6],
    [$0^0 = 1$], [odd $b$], [14], [17.0], [14.5],
  ))

  Every group is within one standard deviation of the refined model. The
  parity doubling is plain: under $0^0 = 0$ the odd bases have 26 solutions
  against 15 in the even ones, while the basic model predicts the same for
  both. The length shares follow @worlds-nega-shares: in even bases most
  solutions have $b - 1$ digits, in odd bases most have $b$ digits.
]

=== Empty bases

Nine bases from $-2$ to $-38$ have no solution under either convention:
$-3$, $-6$, $-9$, $-15$, $-18$, $-20$, $-30$, $-34$ and $-38$. The model
gives each base a chance $exp(-E)$ to be empty, with $E = E_0 + E_1 - E_s$
and $E_s$ the expected number of zero-free solutions, which count in both
conventions. The expected number of empty bases is 4.63, and nine or more
has probability 0.033.

Six of the nine are multiples of 3, which looked like a pattern when the
census stopped at $-35$. The bases $-3$, $-6$, $-9$ were noticed first, so a
fair test leaves them out. Among the multiples of 3 from $-12$ to $-36$,
three of nine are empty against 1.15 expected ($P = 0.095$). The other bases
from $-10$ have three of 20 against 2.44 ($P = 0.45$).

#heuristic(id: "worlds-nega-empty", title: "The empty multiples of 3 are chance", src: ("14.3", "23.2"))[
  Nothing in the arithmetic of the multiples of 3 lowers their chance of a
  solution:
  - The identity modulus $b + 1 equiv 1 med (mod 3)$ gives no factor 3.
  - For $3 | b$ the last digit is fixed modulo 3 by $F$. The exact effect of
    this on the model, measured by sampling, is a factor between 0.9985 and
    1.0006 for $b = 12$ to 39.
  - The near-solution counts of the multiples of 3 match the model, also at
    offsets that keep $n - F(n)$ modulo $b$ and hence modulo 3.

  The excess of empty negative bases is mild and shared by all bases.
]

One side result is worth noting. Offsets that keep the last digit of $n$
give 6% to 23% fewer near-solutions in negative bases than offsets that
only keep the identity. This is the better calibration of the count at
$D = 0$, and against it the solutions of bases $-10$ to $-27$ number 42
against 52. Why the last digit matters here is open (@sec-open-list).

#remark(id: "worlds-nega-recheck", title: "The verdicts with clustered near-solutions", src: ("23.2", "26.4"))[
  Near-solutions at different offsets are not independent: rearranging the
  digits of a number keeps $F$ and moves $n - F(n)$ by a multiple of
  $b + 1$, so one coincidence can be counted at several offsets
  (@ch-model). Recomputed with this clustering, the P values of this
  section become 0.11 for the 42 solutions against 52 (it was 0.09) and
  0.056 for the multiples of 3 against their offsets (it was 0.044). The
  lower near-solution rate at offsets that keep the last digit drops from
  about 4 to about 2.9 standard deviations. The verdicts do not change.
]

== Imaginary, Gaussian and Eisenstein bases <sec-worlds-complex>

=== Imaginary bases reduce to negative bases

#proposition(id: "worlds-imaginary", title: "Imaginary bases", src: "14.4")[
  Let $c >= 2$. A string $S$ is a Munchausen number in base $c i$, with
  digits $0, dots, c^2 - 1$, exactly when its digits at odd positions are
  all 0 and its digits at even positions form a string $t$ of odd length
  $d$ with
  $ "value of" t "in base" -c^2 = F_m (t) + m (d - 1). $
  So $S$ has $2d - 1 equiv 1 med (mod 4)$ digits, and under $0^0 = 0$ the
  Munchausen numbers of base $c i$ and base $-c^2$ correspond one to one.
]
#proof[
  $(c i)^(2k) = (-c^2)^k$ and $(c i)^(2k+1) = c i (-c^2)^k$. So the value of
  $S$ is $A + c i B$, where $A$ is the value of the even-position digits in
  base $-c^2$ and $B$ that of the odd-position digits. $F(S)$ is a positive
  integer, so $B = 0$, and by uniqueness in base $-c^2$ every odd-position
  digit is 0. The top digit sits at an even position, so $S$ has $2d - 1$
  digits, and $d$ is odd by @worlds-odd-length. The $d - 1$ zeros at odd
  positions add $m (d - 1)$ to $F$.
]

Under $0^0 = 1$ the zeros cost something, so the solutions differ from
those of base $-c^2$. Base $2 i$ has $(1, 0, 2, 0, 0)$: its value is
$16 - 8 = 8$, and $1 + 1 + 4 + 1 + 1 = 8$. Base $3 i$ has
$(1, 0, 3, 0, 3)$ and two longer ones, base $4 i$ has $(1, 0, 0, 0, 4)$ and
a 29-digit one, and base $5 i$ has none (#lib("14.4"), computed).

=== Gaussian bases

#theorem(id: "worlds-katai-szabo", title: "Kátai and Szabó", status: "cited", src: "14.5")[
  For $n >= 1$, every Gaussian integer has exactly one finite expansion
  $sum_i a_i beta^i$ in base $beta = -n + i$ with digits
  $a_i in {0, 1, dots, n^2}$ @katai-szabo1975.
]

The last digit of $a + b i$ is $(a + n b) mod (n^2 + 1)$, because
$i equiv n med (mod beta)$. A Munchausen number is a rational integer equal
to the sum of the weights of its digits.

#proposition(id: "worlds-gauss-identity", title: "Gaussian identity", src: "14.5")[
  Every Gaussian integer satisfies $z equiv "digit sum" med (mod beta - 1)$.
  A rational integer is divisible by $beta - 1 = -(n+1) + i$ exactly when
  it is divisible by its norm $M = (n+1)^2 + 1$. So a solution satisfies
  $sum (w(x) - x) equiv 0 med (mod M)$, and no other Gaussian modulus is a
  function of the multiset.
]

$M$ is even exactly when $n$ is even. So @worlds-free-factor predicts
doubling under $0^0 = 0$ in the bases $-2 + i$ and $-4 + i$, and not in
$-1 + i$ and $-3 + i$.

A length bound needs a little more work than in base $b$, because the
digits of a Gaussian integer are produced by repeated division and the
remainders shrink only geometrically. The result is a bound on the length
of a solution: 18, 16, 24 and 38 digits for $n = 1, 2, 3, 4$
(#lib("14.5"), Proposition 14.10, proven with a finite computation).

#computation(id: "worlds-gauss-census", title: "Gaussian bases", src: "14.5")[
  The solutions in bases $-1 + i$, $-2 + i$ and $-3 + i$ are complete up to
  the length bound; base $-4 + i$ is searched up to 22 digits only.

  #align(center, btable(
    columns: 5,
    align: (left, left, right, left, right),
    [base], [$0^0 = 1$], [$E_1$], [$0^0 = 0$], [$E_0$],
    [$-1 + i$], [$(1,1,1,0,0,0,0,0,1) = 9$], [], [six: 2, 3, and four with 9 digits], [],
    [$-2 + i$], [none], [1.05], [$(4,2,4,0,4,1,0,4) = 1029$], [2.22],
    [$-3 + i$], [three with 19 digits, one with 21], [1.11], [the 21-digit one], [1.10],
    [$-4 + i$], [none up to 22 digits], [1.06], [not searched], [2.08],
  ))

  The 21-digit solution of base $-3 + i$ is
  $(1,5,9,2,5,4,9,7,1,3,9,1,9,2,9,1,7,8,2,8,8) = 1989087728$. It has no
  zero, so it counts under both conventions.
]

The counts match the model, with one exception: base $-3 + i$ has four
solutions under $0^0 = 1$ against 1.11 expected ($P = 0.026$). Base
$-4 + i$ is out of reach: the model puts 83% of its mass at 34 digits, and
the prefix test of the search tree does not work, because the numbers with
fixed top digits are not an interval but points of a fractal tile.

Positive integers do not use every length in a Gaussian base. In base
$-2 + i$ no positive integer has 2, 3, 5, 7, 10 or 12 digits, for example.
The lengths come in runs of one parity, and the parity switches about every
$pi slash arctan(1 slash n)$ digits (#lib("14.5"), computed and heuristic).
For base $-1 + i$ the pattern has a clean proof.

#theorem(id: "worlds-minus1i", title: [Base $-1 + i$ is base $-4$ in blocks], src: "23.4")[
  In base $beta = -1 + i$, with digits 0 and 1, the representation of a
  rational integer $n$ is its base $-4$ representation with each base $-4$
  digit $B$ written as the block $(B mod 2, 0, [B >= 2], [B >= 2])$ at
  positions $4j$ to $4j + 3$, least significant first. So a positive
  integer has $8 m + 1$ digits if its leading base $-4$ digit is 1, and
  $8 m + 4$ digits if it is 2 or 3.
]
#proof[
  $beta^4 = -4$. Cut a representation of $z$ into blocks of four digits, so
  that $z = sum_j C_j (-4)^j$ with $C_j = a_0 + a_1 beta + a_2 beta^2 + a_3 beta^3$
  and $a_k in {0, 1}$. Since $beta^2 = -2 i$ and $beta^3 = 2 + 2 i$,
  $ C = (a_0 - a_1 + 2 a_3) + i (a_1 - 2 a_2 + 2 a_3). $
  The imaginary part $y_j$ of $C_j$ lies in ${-2, dots, 3}$. If $z$ is real,
  $sum_j y_j (-4)^j = 0$. Reducing modulo 4 gives $y_0 equiv 0$, so
  $y_0 = 0$, the only multiple of 4 in that range. Divide by $-4$ and repeat:
  every $y_j$ is 0. Now $a_1 - 2 a_2 + 2 a_3 = 0$ forces $a_1 = 0$ and
  $a_2 = a_3$, and $C_j = a_0 + 2 a_2$ is a base $-4$ digit. By uniqueness
  of base $-4$ representations this is the base $-4$ representation of $z$.
  A positive integer has an odd number $2m + 1$ of base $-4$ digits
  (@worlds-odd-length), and its top block ends at position $8m$ or
  $8m + 3$.
]

#corollary(id: "worlds-minus1i-solutions", title: [The solutions of base $-1 + i$], src: "23.4")[
  The Munchausen numbers of base $-1 + i$ with at least two digits are
  2, 3, 4, 5, 6, 7 under $0^0 = 0$, and 9 under $0^0 = 1$.
]
#sketch[
  Under $0^0 = 0$, $F(n)$ is the number of ones, which is the base $-4$
  digit sum $s(n)$. Under $0^0 = 1$, $F(n)$ is the number of digits. With
  $2m + 1$ base $-4$ digits, $n > (4^(2m) - 1) slash 5$, while
  $s(n) <= 3(2m + 1)$ and the length is at most $8m + 4$. So $m <= 1$ and
  $n <= 19$, and a short check finishes the proof.
]

So the census of base $-1 + i$ is complete. The argument needs a power of
$beta$ that is a rational integer. For $-n + i$ with $n >= 2$ no power of
$beta$ is real, and the length runs of those bases remain unproven
(@sec-open-list).

=== Eisenstein bases

Let $omega^2 + omega + 1 = 0$ and $beta = -n + omega$ with $n >= 1$. Then
$beta$ is a root of $t^2 + (2n + 1) t + (n^2 + n + 1)$. A theorem of Kátai
and Kovács and of Gilbert says that such a quadratic is the base of a
canonical number system exactly when $-1 <= 2n + 1 <= n^2 + n + 1$
@katai-kovacs1980 @gilbert1981. So every element of $ZZ[omega]$ has exactly
one expansion with digits $0, dots, n^2 + n$.

#proposition(id: "worlds-eisenstein-identity", title: "Eisenstein identity", src: "21.3")[
  $beta - 1 = -(n+1) + omega$ is primitive of norm $M = n^2 + 3n + 3$. A
  rational integer solution satisfies $sum (w(x) - x) equiv 0 med (mod M)$.
  Since $M = n(n + 3) + 3$, $M$ is odd for every $n$.
]

So @worlds-free-factor predicts no doubling in any Eisenstein base. This
makes them the sharpest test of the claim that the factor 2 follows the
parity of the modulus and not the shape of the base.

#computation(id: "worlds-eisenstein-census", title: "Eisenstein bases", src: "21.3")[
  "near" is the mean number of near-solutions per offset $j M$,
  $j = 1, dots, 30$.

  #align(center, btable(
    columns: 6,
    align: (left, right, right, left, right, right),
    [base], [$M$], [$0^0$], [solutions (lengths)], [model], [near],
    [$-1 + omega$], [7], [0], [none (complete)], [0.79], [],
    [$-1 + omega$], [7], [1], [none (complete)], [1.49], [],
    [$-2 + omega$], [13], [0], [1 (15), complete], [1.22], [1.03],
    [$-2 + omega$], [13], [1], [1 (15), complete], [1.19], [1.07],
    [$-3 + omega$], [21], [0], [2 (12, 25), to 25 of 30 digits], [1.07], [1.27],
    [$-3 + omega$], [21], [1], [2 (23, 25), to 25 of 30 digits], [1.06], [1.13],
    [$-2 + i$ (control)], [10], [0], [1 (8), complete], [2.22], [2.57],
    [$-2 + i$ (control)], [10], [1], [none (complete)], [1.05], [1.07],
  ))
]

The answer is clean. The Eisenstein bases show no doubling: their
near-solution rates under $0^0 = 0$ are 1.03 and 1.27 per offset, against
1.07 and 1.13 under $0^0 = 1$. The Gaussian control with an even modulus
doubles in the same test, 2.57 against 1.07.

== Rational bases <sec-worlds-rational>

In the rational base $p slash q$ of Akiyama, Frougny and Sakarovitch, with
$gcd(p, q) = 1$ and $1 <= q < p$, every positive integer $N$ has exactly one
expansion
$ N = sum_i a_i / q (p / q)^i, quad 0 <= a_i < p, $
found by the recursion $q N_i = p N_(i+1) + a_i$ with $N_0 = N$
@akiyama-frougny-sakarovitch2008. The base $p slash 1$ is the integer base
$p$. A Munchausen number is an $N >= 1$ with $N = sum w(a_i)$. The length of
an expansion grows like $log_(p slash q) N$, while $F$ grows at most
linearly in the length, so each base has finitely many.

#example(id: "worlds-afs-example", src: "16.5")[
  In base $3 slash 2$, $8 = (2, 1, 0, 1, 1)$:
  $ 1/2 + 1/2 dot 3/2 + 1/2 (3/2)^3 + (3/2)^4 = 8 = 4 + 1 + 1 + 1 + 1. $
]

#proposition(id: "worlds-afs-identity", title: "Rational identity", src: ("16.5", "21.2"))[
  Every $N$ satisfies $q N equiv sum_i a_i med (mod p - q)$. A solution
  satisfies $sum (q w(a) - a) equiv 0 med (mod p - q)$. For $q > 1$ there
  are no twins.
]
#proof[
  Modulo $p - q$ we have $p equiv q$, so $q N_i equiv q N_(i+1) + a_i$.
  Summing over $i$ gives $q N_0 equiv q N_L + sum a_i$ with $N_L = 0$. Since
  $gcd(q, p - q) = 1$, the equation $N = F$ turns into the second form.
  Changing the last digit by 1 changes the value by $1 slash q$, which is
  not an integer, so twins cannot occur.
]

If $p$ and $q$ are both odd, $p - q$ is even and
$q w(a) - a equiv w(a) - a equiv 0 med (mod 2)$ under $0^0 = 0$. The
identity holds modulo 2 for free, and the model doubles. If $p$ or $q$ is
even, $p - q$ is odd and nothing doubles. The identity modulus has nothing
to do with the digit range $p$, so this is a clean test.

The integers form a tree under the parent map $N |-> (q N - a_0) slash p$,
and a search walks it from the root. A subtree can be cut when its numbers
grow faster than any sum of weights can follow (#lib("21.2"),
Proposition 21.9, proven). The tree has about $2 (p-1)^(p-1) slash ln(p slash q)$
nodes, so the cost is worst for $q$ near $p$.

#computation(id: "worlds-afs-census", title: [Rational bases with $p <= 11$], src: ("16.5", "21.2"))[
  All bases $p slash q$ with $q > 1$ and $p <= 11$ except $11 slash 8$ and
  $11 slash 10$ were searched exhaustively under both conventions. Totals,
  with "near" the summed mean count of $N = F(N) + j (p - q)$ for
  $j = 1, dots, 30$:

  #align(center, btable(
    columns: 7,
    align: (left, right, right, right, right, right, right),
    [group], [bases], [$0^0 = 0$], [refined], [basic], [near], [$0^0 = 1$ / refined],
    [$p$, $q$ odd], [9], [14], [19.8], [10.0], [19.9], [11 / 9.9],
    [others], [20], [20], [23.4], [23.3], [21.9], [22 / 24.0],
  ))

  Under $0^0 = 1$ the bases with $p <= 8$ have the solutions
  8 and 15 (base $3 slash 2$), 60 and 546 ($5 slash 2$), 583 ($5 slash 3$),
  15227 and 33827 ($6 slash 5$), 96983, 146841 and 103858 ($7 slash 2$,
  $7 slash 3$, $7 slash 4$), 299637 and 346791 ($7 slash 5$), 741782 and
  744115 ($7 slash 6$), 2665246 and 6011678 ($8 slash 5$), and 11673299
  ($8 slash 7$).
]

The near-solutions show the doubling best: 2.2 per offset and base in the
odd/odd bases against 1.1 in the others, under $0^0 = 0$ only, exactly as
the refined model predicts. The solutions themselves fall a little short in
the odd/odd bases, 14 against 19.8 ($P(X <= 14) = 0.11$), while their
near-solutions do not.

== A Pisot base <sec-worlds-pisot>

Let $x >= 1$ and $epsilon = epsilon_x = (x + sqrt(x^2 + 4)) slash 2$, the
larger root of $t^2 - x t - 1$. It is a Pisot unit: its conjugate
$-1 slash epsilon$ has absolute value below 1. This $epsilon$ is also the
unit that controls the family $(1, x, 1)$ in @sec-dio-field. Since
$1 = x slash epsilon + 1 slash epsilon^2$, the greedy expansions in base
$epsilon$ are the strings over $0, dots, x$ in which every digit $x$ is
followed by a 0, except at the end @parry1960. Every positive integer has a
finite greedy expansion @frougny-solomyak1992, possibly with digits after
the point. A Munchausen number is an integer equal to the sum of the
weights of all its digits.

#proposition(id: "worlds-pisot-length", title: "Length", src: "21.4")[
  A positive integer $N$ has at most $2 log_epsilon N + 2$ digits in base
  $epsilon$. So every Pisot base $epsilon_x$ has finitely many solutions.
]
#sketch[
  Let the expansion run from position $k$ down to $-m$. Then
  $N >= epsilon^k$. If $m >= 1$, multiply by $epsilon^m$ and look at the
  conjugate: it equals $N (-1 slash epsilon)^m$, and also a digit
  expansion whose last digit is at least 1. The digit rule bounds that
  expansion below by $1 slash epsilon$. So $N epsilon^(-m) >= 1 slash epsilon$,
  which bounds $m$. A solution has $N <= T x^x$ for $T$ digits, and the two
  bounds together bound $T$ (#lib("21.4")).
]

#proposition(id: "worlds-pisot-identity", title: "Identity and twins", src: "21.4")[
  $epsilon - 1$ has norm $-x$, so $ZZ[epsilon] slash (epsilon - 1) = ZZ slash x$,
  and $epsilon equiv epsilon^(-1) equiv 1$ modulo $epsilon - 1$. Hence
  $N equiv "digit sum" med (mod x)$. Under $0^0 = 0$, if $N$ is a solution
  whose digit at position 0 is 0 and whose digit at position 1 is not $x$,
  then $N + 1$ is a solution. For $x = 1$ the digit at position $-1$ must
  also be 0.
]

There are no self-paying digits: a digit at a position other than 0 adds an
irrational amount to the value. The identity modulus $x$ is even for even
$x$, so @worlds-free-factor predicts doubling there.

#computation(id: "worlds-pisot-census", title: [Pisot bases $x = 1$ to 12], src: "21.4")[
  All solutions, found by enumerating digit multisets up to the length bound
  and checked by direct expansion for $x <= 7$:

  #align(center, btable(
    columns: 3,
    align: (right, left, left),
    [$x$], [$0^0 = 0$], [$0^0 = 1$],
    [1], [2], [9, 12],
    [2], [3, 4, 5], [4, 8, 11, 14],
    [3], [none], [7, 37],
    [4], [9, 10, 54, 55, 84, 138, 312], [10, 138],
    [5], [40, 370], [40, 370],
    [6], [877, 3423, 3475, 6615, 6616, 7031, 50349], [877, 3423, 3475, 6616, 7031],
    [7], [3933, 106077, 917942, 917943], [3933, 870775, 917943],
    [8], [96959, 96960, 917915, 923417, 1787625, 2520454, 2564464, 17697718], [none],
    [9], [405944671], [none],
    [10], [310, 421798810, 877154544, 1600837696, 1956350341, 1956350342], [1956350342],
    [11], [10405164675, 10405164721], [1971580245, 10405164675, 10405164721],
    [12], [none], [none],
  ))

  Summed over $x = 2$ to 12 under $0^0 = 0$: the six even $x$ have 31
  solutions (7 twin pairs) against 17.0 in the refined model and 8.0 in the
  basic one; the five odd $x$ have 9 against 5.4. Near-solutions at the
  offsets $j x$, $j = 1, dots, 30$, number 2.65 per base and offset for
  even $x$ and 1.43 for odd $x$.
]

For the golden ratio ($x = 1$), the first entry reads
$2 = epsilon + epsilon^(-2) = w(1) + w(1)$. The pairs $(N, N + 1)$ in the
table are the twins of @worlds-pisot-identity. The doubling for even $x$ is
plain in the near-solutions. The solutions of even $x$ exceed even the
doubled model, and the twins do not explain this: near-solutions come in
twin pairs at least as often as solutions do.

The calibration explains part of the excess. For even $x$ under
$0^0 = 0$ the offsets $j x$ are not all in the class of 0: offsets with even
$j$ carry 1.4 to 2.4 times as many near-solutions as offsets with odd $j$,
much as the class of 0 is taken modulo $2(b - 1)$ in odd integer bases. So
for even $x$ the class of 0 is, at least in part, the class modulo $2x$, and
the library's offsets $j x$ mixed two classes.

#proposition(id: "worlds-pisot-mod2x", title: "A congruence modulo $2x$", src: "26.6")[
  For even $x$, every positive integer $N$ with digits $d_i$ in base
  $epsilon_x$ satisfies
  $ (N - sum_i d_i) / x equiv A_2 + A_3 med (mod 2), $
  where $A_r$ is the sum of the digits at the positions $i equiv r med (mod 4)$.
]

The proof expands $epsilon^2 = 1 + x epsilon$ and uses
$epsilon^4 equiv 1$ modulo $2x$. The congruence depends on the arrangement
of the digits, not only on their multiset, so it does not by itself give the
factor between the two classes. Its cause is open.

#computation(id: "worlds-pisot-recalibrated", title: [The Pisot excess, recalibrated], src: ("21.4", "26.6"))[
  For $x = 2$ to 8 under $0^0 = 0$, the 25 solutions of even $x$ against the
  near-solutions per offset in the class of 0 modulo $2x$:

  #align(center, btable(
    columns: 3,
    align: (left, right, right),
    [calibration], [mean per offset], [clustered P value],
    [all offsets $j x > 0$], [10.60], [0.0016],
    [even $j$ only], [12.53], [0.0095],
    [local: $D = plus.minus 2 j x$, $j = 1, 2, 3$], [14.83], [0.049],
    [far: $D = plus.minus 2 j x$, $j = 11, dots, 20$], [9.70], [],
  ))

  The defect spectrum peaks near $D = 0$ at the short lengths that hold most
  solutions, so far offsets miss the peak. Under $0^0 = 1$ and for odd $x$
  the excesses that remain (11 against 6.8 and 7 against 2.2 with the local
  calibration, $P = 0.14$ and $0.03$) rest on the tiny solutions of
  $x <= 5$.
]

So the Pisot bases follow the parity law, and with the right class and a
local calibration their excess is a 5% event. The class factor modulo $2x$
is a new structure without an explanation (@sec-open-list).

== Other weights <sec-worlds-weights>

The search engine accepts other weight tables. Two of the resulting
experiments, forced residues and the convention $0^0 = m$ for other $m$,
test the refined model directly and are described in @sec-model-tests. This
section treats three families of weights that occur naturally: $x^(x+t)$,
factorials, and the powers $x^d$ of narcissistic numbers.

=== Two facts behind the length law

The length shares 8, 55 and 23 percent of @heur-length-law rest on two
facts about $w(x) = x^x$:

- the top weight sits at a fixed height between powers of $b$:
  $(b-1)^(b-1) approx b^(b-1) slash e$, so $c$ copies of the top digit cross
  a power of $b$ at $c = e$;
- one digit value lower costs a factor of about $e b$:
  $(b-1)^(b-1) slash (b-2)^(b-2) approx e (b - 1)$.

For $x^(x+t)$ with fixed $t$ both facts hold, with every length moved up by
$t$, and $x^(x+t) equiv x med (mod 2)$. So everything carries over.

#computation(id: "worlds-shift", title: [The weights $x^(x+t)$], src: ("14.6", "17.4"))[
  For $t = -1, 1, 2$ in bases 10 to 32, the totals per convention and base
  parity, the parity factors (about 2 under $0^0 = 0$, 1.2 under
  $0^0 = 1$), the shifted length law, the Poisson dispersion and the number
  of empty bases all match the refined model. For example, for $x^(x+1)$
  under $0^0 = 0$ the even bases have 18 solutions against 14.3 and the odd
  bases 34 against 25.4.
]

=== Factorions

A _factorion_ is a number equal to the sum of the factorials of its digits,
with $0! = 1$. In base 10 the factorions are 1, 2, 145 and 40585
@oeis-a014080. For $x!$ both facts above fail. One digit value lower costs
only a factor $b - 1$, and the height of $(b - 1)!$ between powers of $b$,
$theta(b) = "frac"(log_b (b-1)!)$, moves with $b$.

#heuristic(id: "worlds-factorion-law", title: "Length law of factorions", src: ("14.6", "17.4"))[
  Let $L(b)$ be the number of digits of $(b - 1)!$. For almost all large
  $b$, a factorion has $L(b) - k$ digits with probability about
  $(1 - e^(-lambda)) e^(-k lambda)$, $k = 0, 1, 2, dots$, where
  $lambda approx L(b) slash b = 1 - 1 slash ln b + o(1 slash ln b)$. The shares tend to
  63.2%, 23.3%, 8.6%, 3.2%, a geometric law with ratio $e^(-1)$. The
  expected total is still about 1 per base and convention. There is no
  parity factor.
]

The reason: the weights $(b-1-k)!$ fall by a factor of about $b$ per step,
so the largest digit present fixes the power of $b$, and the number of its
copies only fixes the leading digit. The parity factor disappears because
$x!$ is even for $x >= 2$, so $x! - x$ is odd for odd $x$, and the identity
modulo 2 is a genuine condition. Convergence to the limit is slow, because
$lambda - 1 approx -1 slash ln b$.

#computation(id: "worlds-factorion-census", title: "Factorions in bases 10 to 41", src: ("14.6", "17.4"))[
  The census agrees with OEIS A193163 for bases 2 to 20 @oeis-a193163. In
  bases 10 to 41 there are 37 factorions against 37.1 in the model, and 11
  bases without one against 10.1. The long ones follow the geometric length
  law loosely (9 against 15.8 at the top length $L$); short ones, mostly
  with two digits, are four times too common, like the short Munchausen
  numbers of @sec-short-heuristic. The odd bases from 11 to 41 have 15
  factorions and the even bases from 10 to 40 have 22: no parity effect.
]

=== Narcissistic numbers

A $d$-digit _narcissistic number_ equals the sum of the $d$-th powers of its
digits; 153 is an example in base 10 @oeis-a005188. The weights $x^d$ change
with the length, and so do their residues modulo $b - 1$. This makes the
published lists of narcissistic numbers an outside test of the refined
model, on data that nobody tuned for it.

Two cases are exact. Since $x^d equiv x med (mod 2)$, odd bases get the
factor 2 at every length. And if $x^d equiv x med (mod b - 1)$ for every
digit, for example when $b - 1$ is squarefree and
$d equiv 1 med (mod lambda(b - 1))$, the identity holds for every multiset
and the factor is the full $b - 1$.

#computation(id: "worlds-narcissistic", title: "Narcissistic numbers in bases 3 to 14", src: "19.4")[
  `fast search --power d` finds every narcissistic number with every length
  in bases 3 to 10, up to 62 digits in bases 11 to 13 and up to 50 digits in
  base 14. The counts agree with the OEIS lists. Against the models:

  #align(center, btable(
    columns: 4,
    align: (left, right, right, right),
    [cells], [observed], [basic model], [refined model],
    [all bases 3 to 14], [760], [252.5], [671.3],
    [$d >= 6$, $x^d equiv x med (mod b - 1)$ for all $x$], [207], [24.3], [208.5],
    [$d >= 6$, odd $b$], [354], [100.4], [349.7],
    [$d >= 6$, even $b$], [280], [118.0], [238.3],
    [$d <= 5$], [126], [34.2], [83.3],
  ))
]

The refined model, which adds only the residues, follows the bases from 3 to
189 solutions, where the basic model is off by a factor of 3. In the forced
cells the residue factor reaches $b - 1 = 13$, and the model is right to
1%: base 14 with $d = 49$ has 13 narcissistic numbers, the model expects 9.0
and the basic model 0.69. The deviations are the short lengths, as for
$x^x$, and an excess of about 18% in even bases, mostly from bases 8 and 10.

=== The factorion shortfall in odd bases

One deviation in the factorion data resisted every explanation the library
tried. In the odd bases 14 to 36, long factorions (at least $L(b) - 5$
digits) number 3 under $w(0) = 0$ and 4 under $w(0) = 1$, against about
11.9 and 11.8 in the model.

#computation(id: "worlds-factorion-shortfall", title: "The shortfall against its near-solutions", src: ("17.4", "19.5", "23.1"))[
  Over the odd bases 21 to 35, the mean number of long near-factorions per
  offset, against $D = 0$:

  #align(center, btable(
    columns: 4,
    align: (left, left, right, right),
    [offsets], [keep $n - F(n) equiv 0$ modulo], [$w(0) = 0$], [$w(0) = 1$],
    [$D = 0$ (the factorions)], [everything], [1], [2],
    [model], [], [8.52], [8.37],
    [$j (b - 1)$], [$b - 1$], [8.33], [8.37],
    [$j b (b - 1)$], [$b - 1$, $b$], [8.17], [8.13],
    [$j b^3 (b - 1)$], [$b - 1$, $b^3$], [7.80], [8.20],
    [$j b^2 "lcm"(1, dots, b + 1)$], [all moduli up to $b + 1$, and $b^3$], [8.23], [7.83],
  ))

  Two independent engines and a brute force agree on the census. The fresh
  odd bases 37 to 47, searched after the shortfall was noticed, have 3 long
  factorions per convention against 6.2 expected ($P = 0.13$). Base 47 took
  6292 seconds and has one 34-digit factorion under each convention.
]

#heuristic(id: "worlds-factorion-verdict", title: "An unexplained fluctuation", src: "23.1")[
  A mechanism would have to separate $D = 0$ from every small offset that
  keeps all residues up to $b + 1$ and the last three digits. By
  @thm-only-residue the only residue that the digit multiset fixes is
  $n mod (b - 1)$, and the offsets rule out the low digits and the forced
  top digits. Per offset family and convention the shortfall has
  $P = 0.006$ to 0.025, counted with the clustering of near-solutions
  (@ch-model). After the choice among about 16 groups it has $P approx 0.13$,
  and with the fresh bases combined $P approx 0.09$; an earlier, naive
  calibration gave about 0.05. The library counts it as an unexplained
  fluctuation.
]

== Function fields, and why the model misses there <sec-worlds-ffield>

The polynomial ring $FF_q [T]$ over a finite field is the classic analogue
of the integers (@app-ffield). It has bases, digits and a natural analogue
of $x^x$. This world is special because its weights are additive. The model
of @ch-model gets the count roughly right, but for the wrong reasons, and
the way it fails shows exactly which assumption the model makes.

=== The setting

Let $q$ be a prime and $B in FF_q [T]$ a polynomial of degree $e >= 2$. The
digits are the $q^e$ polynomials of degree below $e$, and every polynomial
$n$ has exactly one expansion $n = sum_i d_i B^i$, by repeated division with
remainder. For a digit $d$ of degree $j$ put $|d| = q^j$, the analogue of
the absolute value, and give $d$ the weight
$ w(d) = d^(|d|) = d^(q^(deg d)), $
with $w(0) = m$. A nonzero constant $c$ has $|c| = 1$ and $w(c) = c$, so the
$q - 1$ constants are the one-digit solutions.

#proposition(id: "worlds-ff-linear", title: "Linearity", src: "21.1")[
  For a digit $d$ of degree $j$, $w(d) = d(T^(q^j))$. Hence
  $ F(n) = sum_(j=0)^(e-1) D_j (T^(q^j)) + m z, $
  where $D_j$ is the sum of the digits of $n$ of degree exactly $j$ and $z$
  is the number of zero digits.
]
#proof[
  In characteristic $p$ the map $y |-> y^q$ is additive, and it fixes the
  coefficients, which lie in $FF_q$. So $d^(q^j) = d(T^(q^j))$, which is
  linear in $d$.
]

So $n$ is a solution exactly when its class sums $(D_0, dots, D_(e-1), z)$
are a fixed point of an explicit map on a finite group, and there are at
most $q^(e(e+1) slash 2)$ solutions, times $q$ if $m = 1$. The problem is
finite and, for a fixed pattern of digit degrees, linear. Two kinds of
structure follow at once.

#proposition(id: "worlds-ff-families", title: "Families and self-paying digits", src: "21.1")[
  Under $0^0 = 0$, if $n$ is a solution, so is $n + c$ for every constant
  $c$; solutions come in families of exactly $q$, which differ only in the
  last digit. A digit $d$ of degree $j >= 1$ pays for itself at position $k$
  when $d^(q^j - 1) = B^k$.
]
#proof[
  $w(d + c) = w(d) + c$ for every digit $d$: if $deg d = j >= 1$, then
  $(d + c)^(q^j) = d^(q^j) + c$, and for constants and 0 both sides equal
  $d + c$. Adding $c$ to $n$ changes only the last digit, so $F$ grows by
  $c$ as well.
]

The families replace the twins of @thm-twins. For example, in base $T^3$
over $FF_2$ the digit $T^2$ pays for itself at position 2, since
$(T^2)^4 = T^8 = T^2 (T^3)^2$.

=== Free residues at every prime

Every $n$ satisfies $n equiv sum_i d_i med (mod B - 1)$, so $B - 1$ is the
identity modulus, and a solution satisfies
$sum_j (D_j (T^(q^j)) - D_j) + m z equiv 0 med (mod B - 1)$
(#lib("21.1"), Proposition 21.5). In the integers the identity holds for
free only modulo 2. Here it holds for free at every prime factor of $B - 1$.

#theorem(id: "worlds-ff-free", title: "Free residues", src: "21.1")[
  Let $P$ be an irreducible factor of $B - 1$, and let $"Tr"$ be the trace
  from $FF_q [T] slash (P)$ to $FF_q$. Then for all class sums $D$,
  $ "Tr"(sum_j (D_j (T^(q^j)) - D_j) mod P) = 0. $
  So under $0^0 = 0$ the identity holds for free on a subspace of
  codimension at least $omega(B - 1)$, the number of distinct irreducible
  factors of $B - 1$.
]
#proof[
  Let $theta$ be a root of $P$ and $sigma$ the Frobenius of $FF_q (theta)$.
  Then $D_j (theta^(q^j)) = sigma^j (D_j (theta))$, because $D_j$ has
  coefficients in $FF_q$, and $"Tr"(sigma^j y) = "Tr"(y)$. Distinct factors
  give independent conditions by the Chinese remainder theorem.
]

For a linear factor $T - a$ the statement reads $D(a^(q^j)) = D(a)$: every
weight agrees with its digit at $a$, just as $x^x equiv x med (mod 2)$. Let
$k(B)$ be the codimension of the image of the identity map; then
$k(B) >= omega(B - 1)$, with equality in all 4,426 bases of the census of
#lib("21.1"). The refined model predicts about $q^(k(B))$ times the basic
count, the analogue of the factor 2.

In degree 2 the count is a formula.

#theorem(id: "worlds-ff-degree2", title: "Degree 2", src: ("21.1", "24.4"))[
  Let $e = 2$. Under $0^0 = 0$, base $B$ has exactly $q (q - 1)$ solutions if
  $B - 1$ has two distinct roots in $FF_q$, and none otherwise. They are the
  numbers $c + beta T^q$ with $c in FF_q$ and $beta != 0$. Under $0^0 = 1$,
  for $q >= 5$, a base with two roots has no solution if
  $B = lambda (T - c)^2$ (proven), and $q (q - 1)$ solutions otherwise
  (computed for $q <= 19$).
]
#sketch[
  Write $D_1 = alpha + beta T$. Then $F = c + beta T^q$ for a constant $c$.
  If $beta = 0$ the sum has one digit. Otherwise the identity gives
  $(B - 1) | beta (T^q - T)$, and $T^q - T$ is the product of all $T - a$, so
  $B - 1$ needs two distinct roots. Conversely, writing
  $(T^q - T) slash (B - 1)$ in base $B$ gives the base-$B$ digits of $F$
  explicitly, and each $beta$ turns out to give exactly $q$ values of $c$.
  Under $0^0 = 1$ the square bases follow from @worlds-ff-conventions
  below: in base $lambda (T - c)^2$ every solution of degree $q$ has
  $(q - 3) slash 2$ or $(q - 1) slash 2$ zero digits, which is not divisible
  by $p = q$. The count $q (q - 1)$ in the other bases is a computation for
  $q <= 19$; its proof is open.
]

#remark(id: "worlds-ff-correction", src: ("21.1", "24.4"))[
  The library first stated that under $0^0 = 1$ and for $q >= 5$ each base
  with two roots has $q (q - 2)$ solutions. That is the average: the
  $q (q-1) slash 2$ square bases $lambda (T - c)^2$ have none, and the other
  bases with two roots have $q (q - 1)$. For $q >= 5$ the census shows 0 or
  $q (q - 1)$ in every such base. For $q = 3$ the average is 5 per base with
  two roots, and the per-base pattern is not established.
]

=== The census and the gap

#computation(id: "worlds-ff-census", title: [Census for $e >= 3$], src: ("21.1", "24.3"))[
  Mean number of solutions per base over all bases of degree $e$, against
  the refined model, which is an exact sum here. The last column is the
  share of $0^0 = 0$ solutions whose number of zero digits is divisible by
  $p$.

  #align(center, btable(
    columns: 9,
    align: (right, right, right, right, right, right, right, right, right),
    [$q$], [$e$], [bases], [$0^0 = 0$], [refined], [$0^0 = 1$], [refined], [ratio], [share $p | z$],
    [2], [5], [32], [3.750], [4.071], [2.125], [3.183], [0.67], [0.57],
    [2], [7], [128], [5.031], [5.026], [3.000], [3.768], [0.80], [0.60],
    [3], [3], [54], [8.222], [6.479], [4.111], [5.477], [0.75], [0.49],
    [3], [4], [162], [14.444], [9.858], [3.778], [8.025], [0.47], [0.26],
    [3], [5], [486], [14.296], [12.924], [5.111], [10.315], [0.50], [0.36],
    [5], [3], [500], [34.400], [26.230], [11.840], [23.338], [0.51], [0.34],
    [5], [4], [2500], [60.480], [45.414], [19.664], [39.674], [0.50], [0.33],
    [7], [3], [2058], [76.286], [64.810], [2.286], [59.438], [0.038], [0.030],
    [11], [3], [13310], [240.000], [233.004], [17.273], [220.000], [0.079], [0.072],
    [13], [3], [26364], [407.077], [379.118], [8.923], [360.982], [0.025], [0.022],
    [17], [3], [78608], [857.412], [835.518], [30.118], [804.398], [0.037], [0.035],
  ))
  The column "ratio" is census over refined model under $0^0 = 1$.
]

Two facts stand out. Under $0^0 = 0$ the model is 3% to 47% too low for
every odd $q$, about 5 standard deviations in all. Under $0^0 = 1$ it is far
too high, and the gap grows with $q$: for $q = 13$ the true count is 2.5% of
the prediction. The model also gets the dependence on $B$ right in one
respect: each factor of $B - 1$ multiplies the count by about $q$
(#lib("21.1"), computed). So the free residue factor is real. Something
else fails.

=== Frobenius builds the digits of F in blocks

The model assumes that the digits of $F$ look like independent uniform
digits. Here they do not, and the reason is that $F$ is a Frobenius image.
Write $Phi(n) = n(T^q) = n^q$.

#lemma(id: "worlds-ff-blocks", title: "Frobenius blocks", src: "24.2")[
  For a digit $d$ write $d(T^q) = sum_r beta_r (d) B^r$ in base $B$. Then
  for every $n = sum_i d_i B^i$,
  $ Phi(n) = sum_i sum_r beta_r (d_i) B^(q i + r). $
  So $Phi$ replaces each digit by its own block of $q$ digits, without
  carries. The digits $beta_r$ with $r > R = floor((e - 1) q slash e)$ are
  zero.
]
#proof[
  The coefficients of $n$, $d_i$ and $B$ lie in $FF_q$, so
  $n^q = sum_i d_i^q (B^q)^i = sum_i d_i (T^q) B^(q i)$. Substituting the
  expansion of $d_i (T^q)$ gives distinct exponents $q i + r$ with digits as
  coefficients, so this is the base-$B$ expansion by uniqueness. Since
  $deg d(T^q) <= (e - 1) q$, the digits above position $R$ vanish.
]

Since $F(x) = D_0 + m z + Phi(D_1 + Phi(D_2 + dots + Phi(D_(e-1))))$, a
Horner form, the whole digit string of $F$ is assembled from $e$ single
digits by repeated blocks (#lib("24.2"), Proposition 24.2 and
Corollary 24.3). Two consequences destroy the independence that the model
assumes.

#corollary(id: "worlds-ff-zeros", title: "Forced zeros and rank one", src: "24.2")[
  + The digit of $F$ at a position $i >= 1$ is zero whenever some base-$q$
    digit of $i$ exceeds $R$. For $e = 3$ and $q > e$ this forces about a
    third of all positions to be zero.
  + For $floor((e-2) q slash e) < r <= R$, all digits of $F$ at the positions
    $i >= 1$ with $i equiv r med (mod q)$ are multiples of one fixed digit
    $tau_r$ of the base, and they add up to $c(x) tau_r$ for a single number
    $c(x) in FF_q$.
]

In the model the digits at the positions of part 2 are about $L slash 3$
independent uniform digits, where $L$ is the length. In truth their total
contribution to the class sums is one number times a fixed vector.

#computation(id: "worlds-ff-digitlaw", title: [The digit law of $F$], src: "24.4")[
  For $q = 5$, $e = 3$, all bases and all full-length class sums, the share
  of each digit degree by position:

  #align(center, btable(
    columns: 5,
    align: (left, right, right, right, right),
    [position], [zero], [degree 0], [degree 1], [degree 2],
    [model], [0.008], [0.032], [0.160], [0.800],
    [0], [0.020], [0.078], [0.102], [0.800],
    [1], [0.066], [0], [0.134], [0.800],
    [2], [0.200], [0], [0.128], [0.672],
    [3, 8, 13], [0.200], [0], [0.800], [0],
    [4, 9, 14], [1], [0], [0], [0],
    [16 (top)], [0], [0], [0], [1],
  ))
  Over the cases $q <= 13$, between 15% and 45% of the digits of $F$ are
  zero, where the model expects $(L - 1) slash q^e$, 4 to 700 times fewer.
]

=== The control that was not a control

The library first judged the gap a fluctuation, because near-solutions
$n = F(n) + (B - 1) g$ with constant or low-degree $g$ matched the census.
That check was not independent.

#lemma(id: "worlds-ff-bijection", title: "Near-solutions that are solutions in disguise", src: "24.4")[
  Let $n$ be a solution under $0^0 = 0$ whose last two digits $d_0$, $d_1$
  have the same degree $j >= 1$, and let $g$ be a digit with $deg g < j$.
  Then $n + (B - 1) g$ has the digits $d_0 - g$ and $d_1 + g$ in place of
  $d_0$, $d_1$, the same class sums, and so it is the near-solution
  $F(x) + (B - 1) g$. This is a bijection between such solutions and such
  near-solutions. Constant offsets give a bijection whenever both digits
  have positive degree.
]
#proof[
  $(B - 1) g$ has the digits $-g$ and $g$ at positions 0 and 1. The digits
  $d_0 - g$ and $d_1 + g$ keep degree $j$, and the class sum of degree $j$
  changes by $-g + g = 0$.
]

In the integers nothing like this happens. Adding $j(b - 1)$ changes the
two lowest digits by $-j$ and $+j$, and it changes $F$ by
$w(d_0 - j) - w(d_0) + w(d_1 + j) - w(d_1) != 0$, because $x^x$ is not
additive. So a small offset does not carry a solution to a near-solution
one for one. Integer near-solutions do cluster in a weaker way: a
rearrangement of the digits keeps $F$ and moves $n - F(n)$ by a multiple of
$b - 1$, and about two thirds of the near-solutions in bases 12 to 26 share
their multiset with a near-solution at another offset (@ch-model). That
inflates the variance of the offset means by a factor 1.5 to 3.5 but not the
means themselves: offsets with no transposition between them give the same
mean within 4%. In $FF_q [T]$, by contrast, the mean itself was the census.
Offsets that randomize
more and more low digits bring the near-solution count down to the model:
for $q = 5$, $e = 3$ it falls from the census value 34.4 per base to 20.1
when 13 low digits can change, against the model's 26.2.

=== The exact channel under $0^0 = 1$

#proposition(id: "worlds-ff-conventions", title: "The conventions", src: "24.4")[
  Let $p$ be the characteristic. If $B - 1$ has an irreducible factor whose
  degree is prime to $p$, then the solutions in base $B$ under $0^0 = 1$ are
  exactly the solutions under $0^0 = 0$ whose number of zero digits is
  divisible by $p$.
]
#proof[
  $F_1(n) = F_0(n) + z(n)$, and $z(n)$ is a constant of $FF_q$. Let $n$ be a
  solution under $0^0 = 1$ and $P$ such a factor. The trace argument of
  @worlds-ff-free, applied to the identity under $0^0 = 1$, gives
  $z deg P = 0$ in $FF_q$, so $p | z(n)$, and then $F_0(n) = F_1(n) = n$. The
  converse is immediate.
]

The census confirms this in 124,257 bases. The refined model takes zeros to
be rare, so it puts the share of solutions with $p | z$ at 0.72 to 0.95. The
true share is the last column of the census table, 0.02 to 0.67, because
most zeros of $F$ are forced (@worlds-ff-zeros) and the rest come in
batches of $q$. With $r_m$ the ratio of census to model under $0^0 = m$,
the proposition gives the exact identity
$ r_1 = r_0 dot ("true share of" p | z) slash (M_1 slash M_0), $
where $M_1 slash M_0$ is close to the model's share. For $q = 5$, $e = 3$:
$1.311 dot 0.344 slash 0.890 = 0.507$, the observed ratio. So the whole gap
under $0^0 = 1$ is the zero count.

=== The channel under $0^0 = 0$

Under $0^0 = 0$ zeros do not matter, and the totals are close, but the
solutions are a different population from the one the model imagines. For
$q = 13$, $e = 3$, 43% of the solutions have $D_1 = 0$, against 2.5% in the
model, and only 1.6% have $D_0 != 0$, against 44%. Constants never occur
above position 0, and the block structure forces the lower class sums.

#proposition(id: "worlds-ff-generic", title: "The generic cell", src: "24.4")[
  Let $0^0 = 0$, $q >= e$ and $q equiv 1 med (mod e)$. Call a class sum $x$
  generic if every digit of $F(x)$ that is neither a forced zero nor at a
  position $equiv R med (mod q)$ has degree $e - 1$. Then a generic $x$ is a
  solution if and only if $D_j = 0$ for all $j < e - 1$ and
  $sigma'^(e-1) (D_(e-1)) = D_(e-1)$, where $sigma'$ is the Frobenius map
  modulo $B - 1$.
]

So on this sector the fixed-point system collapses to the kernel of
$sigma'^(e-1) - 1$ on $FF_q [T] slash (B - 1)$, of dimension
$kappa(B) = sum gcd(e - 1, deg P)$ over the irreducible factors $P$ of
$B - 1$ (for squarefree $B - 1$). The model uses the free factor
$q^(k(B))$ with $k(B)$ the number of factors. The two differ exactly when
some factor of $B - 1$ has a degree that shares a divisor with $e - 1$.

#heuristic(id: "worlds-ff-mechanism", title: "The source of the excess", src: "24.4")[
  The $0^0 = 0$ excess comes from the sector of class sums that the
  Frobenius blocks force. The solutions concentrate there, and where the
  identity restricted to that sector has a larger kernel, $q^kappa$ instead
  of $q^k$, the model is low. Where $B - 1$ splits completely,
  $kappa = k$ and the model is right within 2%: for $q = 13$, $e = 3$ the
  bases with three roots have 2148.6 solutions against 2188.0, while the
  bases with a root and a quadratic factor have 242.0 against 169.7.
]

=== Short solutions for every degree

Call a solution short if $D_j$ is constant for every $j >= 2$. Then
$F = C + b T^q$. The degree-2 count of @worlds-ff-degree2 extends to every
degree.

#theorem(id: "worlds-ff-short", title: "Short solutions", src: "24.5")[
  Let $0^0 = 0$, $e >= 2$ and $q >= e$. If base $B$ has a short solution, then
  $B - 1$ has $e$ distinct roots in $FF_q$. If it does, base $B$ has either
  exactly $q (q - 1)$ short solutions, the numbers $C + b T^q$ with
  $C in FF_q$ and $b != 0$, or none, according to an explicit test on the
  base-$B$ digits of $(T^q - T) slash (B - 1)$. If $e | q - 1$ and
  $B = lambda T^e + mu$ with $(1 - mu) slash lambda$ a nonzero $e$-th
  power, the test passes.
]

=== What the function field teaches

#remark(id: "worlds-ff-lesson", title: "Which assumption fails", src: "24.4")[
  The model of @ch-model assumes that the digits of the sum behave like
  independent uniform digits, subject only to the identity. In $FF_q [T]$:
  - independence fails: the $L$ digits of $F$ come from $e$ single digits,
    and about $1 slash e$ of the positions carry multiples of one fixed digit;
  - uniformity fails: whole positions are always zero or always of one
    degree;
  - the identity modulo $B - 1$ is exact, and the model uses it correctly;
    the error lies in which class sums the solutions have.
  The root cause is that $F$ is additive.
]

In the integers $x |-> x^x$ is not additive, and nothing like the blocks
exists. What remains is the forced top digits of @sec-model-defects: the
largest digits of a multiset fix the leading two or three digits of its
sum.

#computation(id: "worlds-ff-integers", title: "The integer digits of the sum", src: "24.6")[
  For 100,000 random $(b-1)$-digit strings per base, with a $(b-1)$-digit
  sum, in bases 11, 15, 21, 25, 31 and 41, $0^0 = 1$: the top two or three positions of the sum
  are almost never zero or zero far more often than $1 slash b$. Below them
  the rate of zero digits is $1 slash b$ within 3%. The forced top digits move
  the integer predictions by a few percent: the parity factor under
  $0^0 = 1$ by 2% to 4%, and the total by about 1%.
]

One place in the integer data leans the way the toy world does: the long
solutions under $0^0 = 0$ in bases 12 to 41 have 29 zero digits against
42.5 expected, 2.1 standard deviations low. The forced top digits explain 2
to 4 of the missing 13.5. Whether the rest is chance is open
(@sec-open-list).

== The factorial number system <sec-worlds-factorial>

Every $n >= 1$ has exactly one expansion $n = sum_(i=1)^L d_i i!$ with
$0 <= d_i <= i$ and $d_L >= 1$, so $L! <= n < (L + 1)!$. A solution is an
$n = sum_i w(d_i)$. This world has neither a length bound nor an identity.

#proposition(id: "worlds-fact-noresidue", title: "No invariant residue", src: "21.5")[
  No modulus $M >= 2$ makes $n mod M$ a function of the digit multiset on
  the numbers with 3 or more digits.
]
#proof[
  $(1, 0, 1) = 3! + 1 = 7$ and $(1, 1, 0) = 3! + 2! = 8$ have the same
  multiset and differ by 1.
]

#proposition(id: "worlds-fact-selfpaying", title: "Self-paying digits", src: "21.5")[
  A digit $a$ at position $i$ pays for itself, $a dot i! = a^a$, only for
  $(a, i) = (1, 1)$ and $(2, 2)$.
]
#proof[
  We need $a^(a-1) = i!$. For $i >= 3$ take a prime $p >= 3$ with
  $i slash 2 < p <= i$: for $i = 3$ take $p = 3$, and for $i >= 4$ Bertrand's
  postulate gives a prime in that range, which is at least 3. It divides $i!$
  exactly once. Then
  $p | a$, so $p$ divides $a^(a-1)$ at least $a - 1 >= p - 1 >= 2$ times, a
  contradiction. For $i <= 2$, $i!$ is 1 or 2.
]

Under $0^0 = 0$ the solutions $1 = (1)$, $4 = (2, 0)$ and $5 = (2, 1)$ are
the combinations of these two digits, and 4, 5 are twins. Under $0^0 = 1$
the solutions are 1, $2 = (1, 0)$ and $5 = (2, 1)$.

#computation(id: "worlds-fact-census", title: [Census to $34!$], src: "21.5")[
  For $n < 34!$, about $3 dot 10^38$, the only solutions are 1, 4, 5 under
  $0^0 = 0$ and 1, 2, 5 under $0^0 = 1$. The search fixes the counts from
  the largest digit value down, as in @sec-search-tree, and uses that a
  digit $u$ can only sit at a position $>= u$.
]

The windows model predicts $sum_(L = 3)^(33) E_L = 4.5$ solutions per
convention in this range, and about 5.7 more between $34!$ and $301!$.
Zero against 4.5 has probability 0.011. Near-solutions show that this is
not chance: with offsets $D = 1, dots, 100$ there are none for
$7 <= L <= 29$ except one cluster at $L = 26$, and with offsets $D = 1000 j$
the hits sit in 5 of 17 lengths, in clusters of 10 to 50 offsets.

#heuristic(id: "worlds-fact-failure", title: "Why the model fails", src: "21.5")[
  A digit $v$ can only sit at a position $>= v$, and the large digits have
  $v$ close to $L$. So they sit in the few top positions. But the top digits
  of $F$ are fixed by the counts of the large digits,
  $F approx c_v v^v + c_(v-1) (v-1)^(v-1)$, which take only a few values. At
  a given length either these values can place the digit $v$ in a top
  position or they cannot, for all multisets at once. The coincidences come
  all or nothing per length. In integer bases a large digit can sit at any
  position, mostly among the random low digits, and this effect is absent.
]

The model's mean may still be about right: the near-solutions at
$D = 1000 j$ total 218 and 263 against its 231. But their variance is far
larger than Poisson. Whether the factorial system has finitely many
solutions is open; no size argument and no residue are available
(@sec-open-list).

== What is universal <sec-worlds-universal>

@worlds-tab-universal collects the features of all the worlds of this
chapter.

#tablefig(caption: [Features of the number systems and weights. "one per base" means about one coincidence per base and convention before the residue factor.], id: "worlds-tab-universal")[
  #btable(
    columns: 6, size: 8pt,
    align: (left, left, left, left, left, left),
    [world], [one per base], [identity modulus], [free residue factor], [twins], [self-paying digits],
    [integers, $x^x$], [yes], [$b - 1$], [2 if $b$ odd], [yes, $0^0 = 0$], [perfect-power bases],
    [integers, $x^(x+t)$], [yes], [$b - 1$], [2 if $b$ odd], [yes], [yes],
    [factorions $x!$], [yes], [$b - 1$], [none], [triples, $0^0 = 0$], [not studied],
    [narcissistic $x^d$], [yes], [$b - 1$], [up to $b - 1$, by cell], [], [],
    [negative base $-b$], [yes], [$b + 1$], [2 if $b$ odd], [yes], [yes],
    [Gaussian $-n + i$], [yes], [$(n+1)^2 + 1$], [2 if $n$ even], [], [],
    [Eisenstein $-n + omega$], [yes], [$n^2 + 3n + 3$], [none (odd)], [not studied], [no],
    [rational $p slash q$], [yes], [$p - q$], [2 if $p$, $q$ odd], [none for $q > 1$], [no],
    [Pisot $epsilon_x$], [yes], [$x$], [2 if $x$ even], [yes], [no],
    [$FF_q [T]$], [yes, 0.6 to 1.0], [$B - 1$], [$q^(k(B))$], [families of $q$], [yes],
    [factorial], [no: clustered], [none], [none], [yes, at position 1], [only $(1,1)$, $(2,2)$],
  )
]

Three statements summarize the chapter.

#heuristic(id: "worlds-universal-count", title: "Universal laws", src: ("14.6", "21"))[
  + In every world where a digit value can appear at many positions, a base
    has about one coincidence per convention, the count is close to Poisson,
    and a base is empty with probability about $exp(-E)$. The reason is that
    the length of the sum barely depends on the length of the string, so the
    expectations over all lengths add to about 1.
  + The free residue factor follows the identity modulus and the residues
    of the weights. It is 2 exactly when the modulus is even and the weights
    agree with the digits modulo 2. In $FF_q [T]$ it is $q$ per prime of
    $B - 1$.
  + The length shares are not universal. They depend on the height of the
    top weight between powers of the base and on the cost of one digit value
    less: $x^x$ and $x^(x+t)$ give 8/55/23%, even negative bases 8/78/12%,
    odd negative bases and factorions geometric laws with ratios $e^(-2)$
    and $e^(-1)$.
]

The coincidence model itself is not universal. It needs the digits of the
sum below the top to behave like random digits. That fails in the factorial
system, where large digits are tied to the top positions, and in $FF_q [T]$,
where additive weights build the sum from a few blocks. In the integers the
only structure of this kind is the forced top digits, a correction of a few
percent.

A pooled test puts the worlds side by side. Compare, in each world, the
number of solutions with the mean count of near-solutions at offsets in the
class of 0, which measures the real rate of the coincidence without the
model.

#computation(id: "worlds-pooled", title: "A pooled test of the worlds", src: "26.5")[
  Over eight worlds (integer bases 12 to 32, factorions in odd and in even
  bases, negative bases $-10$ to $-27$, rational bases, Pisot bases,
  Eisenstein bases and 2-cycles), 284 solutions stand against 297 to 304
  expected from the near-solutions. The worlds disagree more than chance
  allows: the heterogeneity statistic is 17.2 on 7 degrees of freedom
  ($P = 0.016$) with the Pisot offsets in the class modulo $2x$, and 23.3
  ($P = 0.002$) with the original offsets. Two worlds drive it, the odd-base
  factorions (ratio 0.33) and the Pisot bases. Without these two, the other
  six fit one common ratio, 0.91, with $P = 0.60$ for heterogeneity.
]

So outside the two named worlds nothing suggests that the exact equation
$n = F(n)$ differs from its near misses. Both exceptions were chosen after
looking at the data: the factorion shortfall among about 16 groups, the
Pisot excess as the largest positive deviation.

A last test asked whether one statistic could predict where the model
fails. In every world, compare the low digits of $F(c)$, below its top three,
with the digits that $c$ still needs, and divide by the same agreement for
random low digits. The ratio is within 1.6% of 1 in the integers, base
$-20$, the factorions and the factorial system, within 3.7% in the Pisot
base $epsilon_6$, and 2.2% to 3.4% above 1 per digit value in $FF_5 [T]$
(#lib("26.8"), computed). It does not track the model's error. It is near 1
in the factorial system, where the model fails completely, because that
failure sits in the top digits, and it has the same sign in $FF_q [T]$ under
both conventions, where the model's error changes sign. The failures of the
model live in the top digits or in a single channel such as the zero count,
and an average over the low digits dilutes them.
