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

=== Where the identity modulus comes from <sec-worlds-ideal>

The identity modulus of each world was found world by world. One statement
covers all of them (#q(108)). Take a ring $R$ (the integers, $ZZ[i]$,
$ZZ[omega]$, $ZZ[epsilon]$, $ZZ[1 slash q]$ or $FF_q [T]$), place values
$beta_i$ in $R$, a digit set, and a set of admissible strings. A string has
the value $v(s) = sum s_i beta_i$. An _exchange_ swaps the digits at two
positions of an admissible string and gives another admissible string.

#proposition(id: "worlds-prop-ideal", title: "The invariant ideal", src: "35.3")[
  Let $I_0$ be the ideal generated by the differences $v(s) - v(s')$ of
  admissible strings with the same digit multiset. The multiset fixes the
  value modulo an ideal $I$ exactly when $I$ contains $I_0$.
  + $I_0$ contains every $(x - y)(beta_i - beta_j)$ for an exchange of the
    digits $x, y$ at the positions $i, j$, and is generated by them when the
    admissible strings of each multiset are connected by exchanges.
  + If $beta_i = u beta^i$ with a unit $u$, then
    $v(s) equiv u sum s_i med (mod beta - 1)$. If moreover two adjacent
    positions $i, i + 1$ with $beta^i$ a unit can exchange digits that
    differ by a unit, then $I_0 = (beta - 1)$.
  + If $beta$ is an algebraic integer with monic minimal polynomial $f$,
    then $(beta - 1)$ meets $ZZ$ in $|f(1)| ZZ$. For $beta = p slash q$ or
    $-p slash q$ in $ZZ[1 slash q]$ it meets $ZZ$ in $(p - q) ZZ$ or
    $(p + q) ZZ$.
]
#proof[
  An exchange moves the value by $(x - y)(beta_i - beta_j)$, and along a
  path of exchanges these steps add up. For (2), $beta^i - 1$ is a multiple
  of $beta - 1$, and an adjacent exchange with unit digit difference $e$
  gives $e u beta^i (beta - 1)$. For (3),
  $ZZ[t] slash (f(t), t - 1) = ZZ slash f(1)$, and $p slash q - 1$ is a
  unit times $p - q$ in $ZZ[1 slash q]$.
]

So the identity modulus of a geometric system is $|f(1)|$: $b - 1$ for
$beta = b$, $b + 1$ for $-b$, $(n + 1)^2 + 1$ for $-n + i$, $n^2 + 3n + 3$
for $-n + omega$, $x$ for $epsilon_x$ (where $f = t^2 - x t - 1$), $p - q$
for $p slash q$. The digit differences matter: with only even digits the
ideal would be $2(beta - 1)$. The offsets of the swap lemma
(@model-lem-swap) live in the same ideal.

#proposition(id: "worlds-prop-index", title: "The residue factor is an index", src: "35.3")[
  Suppose $v(s) equiv u sum s_i$ modulo $I_0$ and $R slash I_0$ is finite.
  Put $g(x) = w(x) - u x$, and let the digits of a string be independent
  with a fixed law that charges a digit with $g = 0$. If $H$ is the subgroup
  of $R slash I_0$ generated by the $g(x)$ of the digits that occur, then
  $P(sum g(x_i) equiv 0) -> 1 slash |H|$, and the refined model gains the
  factor $[R slash I_0 : H]$.
]
#proof[
  The partial sums are a random walk on $H$ that can stay put and whose
  steps generate $H$, so they become uniform on $H$.
]

The parity doubling is the index 2 when every $g(x)$ is even. The factor
$q^(k(B))$ of $FF_q [T]$ is the index cut out by the trace conditions
(@sec-worlds-ffield). The factorial system has $I_0 = ZZ$ and no factor.

#computation(id: "worlds-comp-ideal", title: "The predicted moduli in 67 systems", src: "35.3")[
  Group the integers of a range by their digit multiset and take the gcd of
  all differences within groups. In integer bases 3 to 12, negative bases
  $-2$ to $-10$, bijective bases 2 to 10, balanced bases 3 to 9, ten
  rational bases $p slash q$, seven bases $-p slash q$, Gaussian bases
  $-n + i$ ($n <= 5$), Eisenstein bases $-n + omega$ ($n <= 4$), Pisot bases
  $epsilon_x$ ($x <= 8$) and the factorial system, the gcd is the predicted
  modulus every time.
]

Two predictions follow for worlds not yet searched. Bijective base $b$,
with digits 1 to $b$ and no zero, has the identity modulus $b - 1$, and in
odd bases the factor 2 with no convention to choose (#q(95)). Balanced
ternary has the modulus 2 and the base $-3 slash 2$ the modulus 5.

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
$-32$. For $x >= 4$ odd or a square, $(x, 0, 0)$ and $(x, 0, 1)$ are solutions in base
$-x^((x-1) slash 2)$ as well as in base $x^((x-1) slash 2)$ (for $x = 3$ the
base is $-3$, which has no digit 3). This gives
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
$j$ carry 1.5 to 2.4 times as many near-solutions as offsets with odd $j$,
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
factor between the two classes. Its cause is open. It is not an invariant of the multiset
either: for $x = 4, 6, 8$ and $N < 8000$ the gcd of the differences within
multiset groups is $2x$ only at length 4, and $x$ at every other length
#lib("35.3"). So the class effect is a bias of the greedy expansions.

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
  with two digits, are four times too common. Short Munchausen numbers
  are about 3 times too common on generic strings against the exact refined
  model (@sec-short-arrangements). The odd bases from 11 to 41 have 15
  factorions and the even bases from 10 to 40 have 22: no parity effect.
]

For a fixed number of digits, short factorions obey exact theorems
(@sec-worlds-short-factorions). For example, every $x >= 3$ gives the
2-digit factorion $(1, x)$ in base $x! - x + 1$.

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

Length 2 can be solved exactly, and the answer comes from the theory of sums of two squares (@sec-app-quadratic-two-squares). The 2-digit narcissistic numbers are also the 2-digit fixed points of the map "sum of the squares of the digits", known from happy numbers.

#theorem(id: "worlds-narc-two", title: "Two-digit narcissistic numbers", src: "30.3")[
  For every $b >= 2$, base $b$ has exactly $tau(b^2 + 1) - 2$ two-digit narcissistic numbers, where $tau$ counts divisors.
]
#proof[
  A 2-digit narcissistic number satisfies $s_1 b + s_0 = s_1^2 + s_0^2$ with digits $1 <= s_1 <= b - 1$ and $0 <= s_0 <= b - 1$. Multiply by 4 and complete the squares:
  $ (2 s_1 - b)^2 + (2 s_0 - 1)^2 = b^2 + 1 . $
  So a solution gives a representation $b^2 + 1 = A^2 + B^2$ with $B = 2 s_0 - 1$ odd. Conversely, take a representation with $B$ odd and positive. Then $A^2 equiv b^2 med (mod 2)$, so $s_1 = (A + b) slash 2$ is an integer. If $B = 1$, then $A = plus.minus b$, and $s_1$ is 0 or $b$, not a digit. If $B >= 3$, then $|A| <= b - 2$, so $s_1$ is a digit, and $B <= b$ makes $s_0 = (B + 1) slash 2$ a digit. So the solutions correspond to the representations with $B$ odd and positive, minus the two with $B = 1$.

  Count them with @app-quadratic-r2. If $b$ is even, $b^2 + 1$ is odd, $r_2 = 4 tau(b^2 + 1)$, and exactly one of $A$, $B$ is odd. Swapping $A$ and $B$, and changing the sign of $B$, shows that a quarter of the representations have $B$ odd and positive: $tau(b^2 + 1)$ of them. If $b$ is odd, $b^2 + 1 = 2 m$ with $m$ odd, $r_2 = 4 tau(m)$, both $A$ and $B$ are odd, and half of the representations have $B > 0$: that is $2 tau(m) = tau(b^2 + 1)$. In both cases subtract 2.
]

Base 10 has none, because 101 is prime. That is why the base-10 list of narcissistic numbers jumps from 9 to 153 @oeis-a005188.

#corollary(id: "worlds-narc-two-cor", title: "Empty bases and Landau's problem", src: "30.3")[
  + Every odd base $b >= 3$ has at least two 2-digit narcissistic numbers.
  + An even base has none exactly when $b^2 + 1$ is prime. So "infinitely many bases have no 2-digit narcissistic number" is equivalent to Landau's open problem whether $n^2 + 1$ is prime for infinitely many $n$.
  + Infinitely many bases have at most two.
  + The mean number over the bases $b <= X$ is $(3 slash pi) ln X + O(1)$.
]
#proof[
  (1) $b^2 + 1 = 2 m$ with $m > 1$ odd, so $tau(b^2 + 1) >= 4$. (2) The count is 0 exactly when $tau(b^2 + 1) = 2$, that is, when $b^2 + 1$ is prime. For odd $b > 1$ the number $b^2 + 1$ is even and larger than 2, so only even $b$ can give a prime. (3) By Iwaniec's theorem, infinitely many $b^2 + 1$ have at most two prime factors, and then $tau(b^2 + 1) <= 4$. (4) Hooley's theorem. Both theorems are in @sec-app-quadratic-two-squares.
]

The parity effect of @model-heur-parity is a theorem here.

#proposition(id: "worlds-narc-parity", title: "The parity doubling is exact", src: "30.3")[
  The mean number of 2-digit narcissistic numbers is $(2 slash pi) ln X + O(1)$ over the even bases $b <= X$, and $(4 slash pi) ln X + O(1)$ over the odd ones.
]
#sketch[
  Write $tau(n^2 + 1)$ as twice the number of divisors $d <= n$, and let $nu(d)$ be the number of square roots of $-1$ modulo $d$. Summing over $n <= X$ of one parity and exchanging the sums gives sums of $nu(d) slash d$ over $d$, up to $O(X)$. An odd $d$ divides $n^2 + 1$ equally often for even and odd $n$. An even $d$ is $2 d'$ with $d'$ odd, because 4 never divides $n^2 + 1$, and it forces $n$ odd. The even $d$ add $X sum_(d' <= X slash 2) nu(d') slash d'$ to the odd $n$, which equals the share of the odd $d$ up to $O(X)$. So the odd bases get twice the sum of the even bases, up to $O(X)$, and Hooley's total fixes the constants.
]

So the factor 2 of odd bases is the prime 2 dividing $b^2 + 1$, which happens exactly when $b$ is odd. In the refined model the same factor comes from $x^2 equiv x med (mod 2)$.

#computation(id: "worlds-narc-two-comp", title: [Two-digit narcissistic numbers up to $10^6$], src: "30.3")[
  Means of $tau(b^2 + 1) - 2$ over the bases $b <= X$:
  #align(center, btable(columns: 6, align: (right,) * 6,
    [$X$], [even $b$], [$(2 slash pi) ln X$], [odd $b$], [$(4 slash pi) ln X$], [even $b$ with none],
    [$10^2$], [1.720], [2.932], [5.102], [5.863], [36.0%],
    [$10^3$], [3.136], [4.398], [7.896], [8.795], [22.2%],
    [$10^4$], [4.630], [5.863], [10.797], [11.727], [16.8%],
    [$10^5$], [6.088], [7.329], [13.735], [14.659], [13.3%],
    [$10^6$], [7.555], [8.795], [16.670], [17.590], [10.8%],
  ))
  A brute force over all digit pairs agrees with @worlds-narc-two for every $b <= 400$.
]

Both means grow at the predicted rates, with constant terms of about $-1.2$ and $-0.9$. The coincidence model misses this growth. It gives a 2-digit string a chance that does not depend on $b^2 + 1$, so its mean stays bounded, while the truth grows like $ln b$. The missing factor is local. Modulo an odd prime $ell$, the conic $A^2 + B^2 equiv b^2 + 1$ has $ell - chi(ell)$ points if $ell divides.not b^2 + 1$. If $ell | b^2 + 1$, it splits into the two lines $A equiv plus.minus i B$ and has $2 ell - 1$ points. So each prime factor of $b^2 + 1$ roughly doubles the expected count. These are the local factors of the root heuristic (@sec-short-heuristic) in their simplest exact case. In bases 3 to 14 the 2-digit counts sum to 22, against 14.4 in the refined model. That is part of the excess of short narcissistic numbers in @worlds-narcissistic. No analogue of @worlds-narc-two is known for 3 digits, where the equation is a cubic surface (#q(122)).

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

The local arguments of @sec-worlds-short-factorions do not reach this
question. They need one digit much larger than the others, and a long
factorion has many digits of similar size.

== Short factorions and Brocard's problem <sec-worlds-short-factorions>

For a fixed number of digits, a factorion is a root of one polynomial
equation in the base, as in @ch-short. For the weight $x!$ this equation
has a feature that $x^x$ lacks: $x!$ is divisible by every prime up to
$x$. This gives congruences that get stronger as the digit grows, and with
them theorems about short factorions in all bases at once #lib("33.1",
"33.2"). Where the congruences stop, a famous open problem takes over:
Brocard's equation $n! + 1 = m^2$. In this section $w(x) = x!$ for
$x >= 1$, and $w(0) = 1$ (the usual $0! = 1$) or $w(0) = 0$.

=== Two digits

#proposition(id: "worlds-fact-two", title: "Infinitely many 2-digit factorions", src: "33.2")[
  For every $x >= 3$ the string $(1, x)$ is a factorion in base
  $b = x! - x + 1$, under either convention.
]
#proof[
  The value is $b + x = x! + 1 = w(1) + w(x)$, and $b > x$ for $x >= 3$.
]

So 2-digit factorions are infinitely many, as 2-digit Munchausen numbers
are (@sec-cons-two-digit). The interesting lengths start at 3.

=== Three digits: a square modulo every small prime

Take a 3-digit string with a large digit $x$ and two digits at most $B$.
Multiply the equation by 4 times the leading digit and complete the square,
as in @sec-short-square. For a large last digit, $(p, q, x)$ in base $b$,
$
  (2 p b + q)^2 = 4 p dot x! + K(x), quad K(x) = q^2 + 4 p (w(p) + w(q) - x).
$
The other positions give the same shape with another $K$:
- middle, $(p, x, r)$: $(2 p b + x)^2 = 4 p dot x! + K(x)$ with
  $K(x) = x^2 + 4 p A$ and $A = w(p) + w(r) - r$;
- leading, $(x, q, r)$: $(2 x b + q)^2 = 4 x dot x! + K(x)$ with
  $K(x) = q^2 + 4 x A$ and $A = w(q) + w(r) - r$.

In all three cases $K(x)$ is small: of size about $x$ or $x^2$. The
dominant term is a multiple of $x!$.

#lemma(id: "worlds-fact-local", title: "A square modulo every small prime", src: "33.1")[
  If $U^2 = c dot x! + K$ for integers $U$, $c$ and $K$, then $K$ is a
  square modulo every prime $ell <= x$. In particular, if some odd prime
  $ell <= x$ does not divide $K$ and $K$ is not a square modulo $ell$, then
  there is no solution.
]
#proof[
  A prime $ell <= x$ divides $x!$, so $U^2 equiv K med (mod ell)$.
]

The library uses a sharper form with $ell$-adic numbers (@app-padic). It
also covers primes that divide $K$ to a low power, and the prime 2
(Lemmas 33.1 and 33.2 of #lib("33.1")). For the weight $x^x$ nothing of the
kind holds. The term $4 p x^x$ is divisible only by the primes of $p$ and
$x$, so modulo most primes it runs through many residues as $x$ varies, and
no finite set of congruences bounds the large digit (@sec-short-local).

So everything depends on one question: if $K(x)$ is not a perfect square,
is there a prime $ell <= x$ modulo which it is not a square? Write
$K = f^2 D$ with $D$ squarefree. A prime that is inert in the quadratic
field $QQ(sqrt(D))$ and does not divide $f$ does the job. The least inert
prime of a quadratic field is small: below 80 for every discriminant up to
$4 dot 10^6$ in absolute value, and at most a small power of the
discriminant in general (@sec-app-quadratic-inert). Since $abs(K(x))$ grows
only like $x$ or $x^2$, the least inert prime is far below $x$ once $x$ is
large.

#theorem(id: "worlds-fact-three", title: "Three-digit factorions with one large digit", src: "33.1")[
  Fix the convention, the position of the large digit $x$, and the two
  other digits.
  + If $x$ is the last or the middle digit, only finitely many $x$ give a
    factorion, and there is an explicit bound.
  + If $x$ is the leading digit, the same holds for the $x$ with $K(x)$ not
    a perfect square. If $K(x) = s^2$, the string is a factorion exactly
    when $4 x dot x! + s^2 = U^2$ for an integer $U equiv q med (mod 2x)$
    with $(U - q) slash (2x) > x$. There are infinitely many such $x$,
    about $sqrt(X)$ of them up to $X$.
  When the two other digits are at most $B$, the bounds hold uniformly in
  $B$. They grow like a power of $B!$, and like a polynomial in $B$ under
  the generalized Riemann hypothesis (@sec-app-galois-effective).
]
#sketch[
  First the $x$ with $K(x)$ a perfect square. In the last position
  $K(x) < 0$ once $x > w(p) + w(q) + q^2 slash (4p)$, so these $x$ are
  finitely many. In the middle, $x^2 + 4 p A = t^2$ means
  $(t - x)(t + x) = 4 p A$ with $A >= 1$, which has finitely many solutions.
  In front, $q^2 + 4 A x = s^2$ holds for every $x = (s^2 - q^2) slash (4A)$
  that is an integer, infinitely often. (If $A = 0$, which happens only
  under $w(0) = 0$, then $4 x dot x!$ would be a square. But by Bertrand's
  postulate a prime in $(x slash 2, x)$ divides it exactly once.)

  For the other $x$, apply @worlds-fact-local with the least inert prime
  $ell_0$ of $QQ(sqrt(K(x)))$. The bounds of @sec-app-quadratic-inert give
  $ell_0$ of size at most about $x^(0.9)$, below $x$ for large $x$. If
  $ell_0$ divides $f$, the field has a smaller discriminant, and the
  $ell$-adic form of the lemma excludes $x$ once $x$ is a little larger
  than $ell_0 log_(ell_0) abs(K)$. A computer finds the point $X_0$ beyond
  which all of this holds.
]

#tablefig(caption: [The bound $X_0 (B)$ beyond which a 3-digit factorion with one large digit and the other two at most $B$ needs $K(x)$ to be a perfect square, unconditionally and under GRH #lib("33.1").], id: "tab-worlds-fact-x0")[
  #btable(columns: 7, align: (right, right, right, right, right, right, right),
    [$B$], [last], [last, GRH], [middle], [middle, GRH], [leading], [leading, GRH],
    [5], [60,640], [241], [1,340], [1,340], [137], [137],
    [10], [$1.28 dot 10^6$], [2,158], [17,560], [2,158], [$4.42 dot 10^6$], [4,626],
    [20], [$3.0 dot 10^(12)$], [23,380], [$3.8 dot 10^9$], [23,380], [$2.1 dot 10^(16)$], [37,650],
    [100], [$3.9 dot 10^(83)$], [$6.5 dot 10^6$], [$4.6 dot 10^(72)$], [$6.5 dot 10^6$], [$3.4 dot 10^(130)$], [$7.1 dot 10^6$],
  )
]

Below the bound, the remaining $x$ can be checked one by one. This gives
the complete list for small digits, up to the leading case.

#computation(id: "worlds-fact-list", title: "Three-digit factorions with two digits at most 10", src: "33.1")[
  Let $s$ be a 3-digit factorion, under either convention, whose digits
  other than one digit $x$ are at most 10. Then $s$ is one of
  - $(1, 4, 4)$ in base 5, $(1, 4, 5)$ in base 10, $(6, 6, 1)$ and
    $(6, 6, 2)$ in base 15, $(7, 2, 5)$ in base 27, $(1, 6, 6)$ in base
    35, $(2, 4, 10)$ in base 1346,
  - $(6, 6, 0)$ in base 15 under $w(0) = 0$,
  or $s = (x, q, r)$ with $x > 4","103","641$, $K(x) = s'^2$ a perfect square
  and $4 x dot x! + s'^2$ a perfect square.

  The check covers 679 cases (convention, position, two digits). Every
  $x <= 400$ is tested exactly. Every $x$ up to $X_0$ with $K(x)$ not a
  square is excluded by a prime below 300 or, for a few $x$, by a larger
  prime. The 211,668 values of $x$ with $K(x)$ a square and $x > 3000$
  are sieved: $c dot x! + s^2$ must be a square modulo 40 primes above $x$,
  where $x!$ is a unit. None survives.
]

The solution $(2, 4, 10)$ in base 1346 is the square case of the last
position: $K(10) = 144 = 12^2$, and the equation reads
$10! slash 2 + 9 = 1347^2$. Its digits are small, so earlier searches over
all strings with digits up to 150 already found it. What is new is that no
large third digit, in any base, adds a factorion, except possibly in the
leading case.

=== Brocard's problem

In 1876 Brocard asked for all solutions of $n! + 1 = m^2$. The known ones
are $n = 4, 5, 7$, and Berndt and Galway found no other with
$n <= 10^9$ @berndt-galway2000. Whether there are finitely many is open.
The leading case of @worlds-fact-three is a problem of the same kind:
$4 x dot x! + s^2 = U^2$ asks for two divisors $U - s$ and $U + s$ of
$4 x dot x!$ that differ by only $2s$, about $4 sqrt(A x)$. Brocard's
equation asks for two divisors $m - 1$ and $m + 1$ of $n!$ that differ
by 2.

The argument of @worlds-fact-local is due, for a fixed constant, to
Dabrowski @dabrowski1996: $x! + A = y^2$ has finitely many solutions when
$A$ is not a square, by one fixed prime $ell$ modulo which $A$ is not a
square. Here $K(x)$ moves with $x$, so one needs a bound for the least
inert prime instead of one fixed prime. When $A$ is a square, as in
Brocard's equation, no prime helps: every $U^2 = c dot x! + s^2$ is
solvable modulo every prime. This is where congruences stop.

Under the abc conjecture (@app-abc), Brocard's equation has only finitely
many solutions (Overholt @overholt1993), and so does the leading case.

#corollary(id: "worlds-fact-abc", title: "The Brocard case under abc", status: "conditional", src: "33.1")[
  Assume the abc conjecture. Then for fixed $q$ and $r$ only finitely many
  leading digits $x$ give a factorion $(x, q, r)$. Assume the explicit form
  $c < "rad"(a b c)^(7 slash 4)$ (@sec-app-abc-explicit). Then the leading
  case of @worlds-fact-list does not occur, and the list there is
  complete.
]
#sketch[
  Put $N = 4 x dot x!$ and $R = s^2$, and divide $N + R = U^2$ by
  $g = gcd(N, R)$. The radical of the triple is at most
  $"rad"(N) dot U dot R$. Here $"rad"(N)$ is the product of the primes up
  to $x$, about $e^x$, while $ln N$ is about $x ln x - x$, and $U$ is about
  $sqrt(N)$. So abc gives
  $(x ln x - x) slash 2 lt.tilde (1 + epsilon) x + O(ln x)$, which bounds
  $x$. With the
  exponent $7 slash 4$ the inequality reads
  $ln N < 7 ln 2 + 14 ln("rad"(N) R)$. Since $ln "rad"(N) < 1.01624 x$
  @rosser-schoenfeld1962, this fails for $x > 4","103","641$, where
  $x ln x - x$ overtakes $14.23 x$.
]

So for three digits the factorion problem is solved up to a question of
Brocard type, and that question is finite under abc. This is as far as
current methods go.

Two large digits $u <= v$ and one small digit lead to the same kind of
equation. Under GRH the congruence argument works with $M = 4 d (u! + v!)$
when $v$ is at most about $u^3$, and with $M = 4 d dot v!$ above that,
where $d$ is the leading digit. What it leaves are equations
$U^2 - t^2 = 4 d (u! + v!)$ and $U^2 - t^2 = 4 d dot v!$, again of Brocard
type (Proposition 33.8 of #lib("33.1")). Without GRH a range between
$v approx u^(1.1)$ and $v approx (u!)^(0.45)$ is out of reach.

=== Longer factorions

For $k >= 4$ digits the completed square is no longer available, but the
congruence argument still works with the polynomial of the string. Fix a
prefix $t = (t_0, dots, t_(k-2))$ of digits at most $B$, with $t_0 >= 1$,
and let the last digit $x$ be large. With $P_t$ the value polynomial of
the prefix (@sec-basics-polynomial) and $F(t)$ the sum of its weights, the
string $(t, x)$ is a factorion in base $b$ exactly when
$
  G_x (b) = x!, quad G_x (r) = r P_t (r) + x - F(t).
$
If $G_x$ has no root modulo some prime $ell <= x$, there is no solution. By
the Chebotarev density theorem (@app-galois), $G_x$ has no root modulo a
positive share of the primes, unless it has a root modulo every prime. The
question is whether such a prime lies below $x$.

#theorem(id: "worlds-fact-grh", title: "A large last digit under GRH", status: "conditional", src: "33.2")[
  Assume the generalized Riemann hypothesis. Let $k >= 3$ and let the
  prefix $t$ have digits at most $B$. There is an effective constant $c_k$
  with the following property. If
  $x >= c_k (ln x + B ln B)^2 (ln ln x + ln B)^2$ and $G_x$ has no root
  modulo some prime, then $(t, x)$ is a factorion in no base. For
  $k <= 5$, $G_x$ has a root modulo every prime only when it has a rational
  root. Up to $X$ this happens for $O(X^(1 slash (k-1)))$ values of $x$.
]
#sketch[
  The discriminant of $G_x$ has logarithm of order $ln x + B ln B$. Under
  GRH, Lagarias and Odlyzko @lagarias-odlyzko1977 count the primes up to
  $X$ whose Frobenius element fixes no root, with an error of order
  $sqrt(X)$ times logarithms. For $X$ of the stated size this count exceeds
  the number of primes that divide the discriminant. So some prime
  $ell <= x$ has no root of $G_x$ and divides $x!$, a contradiction. For
  degree at most 4, Jordan's theorem (@app-galois-jordan) and a short
  check of products of two quadratics show that a fixed-point-free element
  exists unless $G_x$ has a linear factor. A rational root $-u slash v$ has
  $v | t_0$, and then $x$ is a polynomial of degree $k - 1$ in $u$.
]

For $k = 3$ the rational-root values of $x$ are finitely many, and
@worlds-fact-three is the unconditional form. For $k = 4$ and 5 they are
infinitely many. For such $x$ the polynomial factors as
$G_x (r) = (v r + u) H(r)$, and the factorion equation becomes
$(v b + u) H(b) = v dot x!$: two factors of a factorial in a fixed
proportion, a problem of Brocard type again. So GRH alone does not prove
that 4-digit factorions are finitely many. The abc conjecture does, for
each fixed prefix (@cons-abc-dominant with @cons-factorial-powers).

#computation(id: "worlds-fact-four", title: "Four-digit factorions with a large last digit", src: "33.2")[
  For all prefixes $(p, q, s)$ with digits up to 6, both conventions and
  $2 <= x <= 1500$ (881,412 strings), there is no 4-digit factorion. Where
  a prime $ell <= x$ without a root of $G_x$ exists, the least one is at
  most 101, and 2, 3 and 5 settle 65% of these strings. Every $x >= 76$
  without such a prime has $G_x$ with a rational root, as
  @worlds-fact-grh says.
]

The GRH bound is far from tight here. The least prime without a root
behaves like a random variable with a geometric tail, not like
$(ln x)^2$.

#conjecture(id: "worlds-fact-finite", title: "Finitely many factorions of each length", src: "33.2")[
  For each $k >= 3$ there are only finitely many $k$-digit factorions.
]

The root heuristic (@sec-short-heuristic) gives a string with largest
digit $M$ a chance of about $(M!)^(-(k-2) slash (k-1))$, and there are
about $M^(k-1)$ such strings. The sum over $M$ converges very fast. Unlike
for $x^x$, no identity family can make it diverge, because $x!$ is almost
never a power (@cons-factorial-powers).

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
$k(B)$ be the codimension of the image of the identity map
$D |-> sum_j (D_j (T^(q^j)) - D_j) mod (B - 1)$. Then
$k(B) >= omega(B - 1)$, and the refined model predicts about $q^(k(B))$
times the basic count, the analogue of the factor 2.

=== The free residue dimension

Is $k(B)$ exactly the number of factors? In most cases yes, and the proof
is linear algebra with Frobenius on $R = FF_q [T] slash (B - 1)$
(@sec-app-ffield-local). Let $t$ be the class of $T$ in $R$ and
$phi(x) = x^q$. A class sum $D_j$ of degree at most $j$ is a polynomial in
$t$ of degree at most $j$, and $D_j (T^(q^j))$ reduces to $phi^j (D_j)$. So
the image of the identity map is
$ J = sum_(j = 1)^(e - 1) (phi^j - 1) W_j, $
where $W_j$ is the span of $1, t, dots, t^j$, and $k(B) = e - dim J$. Call
an irreducible factor $P$ of $B - 1$ _good_ if $gcd(deg P, e - 1) = 1$.

#theorem(id: "worlds-ff-kB", title: [$k(B)$ is the number of factors], src: "29.2")[
  + If $B - 1$ has a good factor, then $k(B) = omega(B - 1)$.
  + If $e = 2$, or $e - 1$ is a prime power, then $k(B) = omega(B - 1)$ for
    every base $B$ of degree $e$. This covers
    $e = 2, dots, 6, 8, 9, 10, 12, 14, dots$.
  + In every case $k(B) <= omega(B - 1) + 1$, and $k(B) = omega(B - 1)$
    when $B - 1$ is not squarefree.
]
#sketch[
  (1) Since $phi^j - 1 = (phi - 1)(1 + phi + dots + phi^(j-1))$, the space
  $J$ lies in the image $I$ of $phi - 1$, which has codimension
  $omega(B - 1)$ by fact 1 of @sec-app-ffield-local. The term $j = e - 1$
  has $W_(e-1) = R$, and on a good factor its image is already the image of
  $phi - 1$ (fact 4 with $S = {e - 1}$). The bad factors have total degree
  at most $e - 1$, so the spaces $W_j$ with $j >= e - 2$ reach every class
  modulo their product. There the two consecutive exponents $e - 2$ and
  $e - 1$ give the image of $phi - 1$ again (fact 4). So $J$ contains the
  good part of $I$ and projects onto the bad part of $I$, and therefore
  $J = I$.
  (2) For $e = 2$ every degree is prime to $e - 1 = 1$, so every factor is
  good. Otherwise, if every factor were bad, a prime $r$ dividing $e - 1$
  would divide every degree, hence $e = sum a_i deg P_i$, and also $e - 1$.
  (3) Pass to linear functionals. A functional vanishes on $J$ when it is
  invariant under $phi^j$ on $W_j$ for each $j$. The difference
  $lambda compose phi - lambda$ of such a functional is forced onto one
  line, which gives at most one dimension beyond the $phi$-invariant
  functionals. When $R$ has a nilradical, the conditions for that extra
  dimension make a nondegenerate pairing vanish on it, which is impossible.
]

The library also excludes the extra dimension for squarefree $B - 1$ when
$q <= e - 2$, and by hand for the remaining factor types of degree 7. So
$k(B) = omega(B - 1)$ holds for every $e <= 10$ and for every base of every
census, by proof (#lib("29.2")).

#computation(id: "worlds-ff-kB-comp", title: [$k(B)$ by computation], src: "29.2")[
  $k(B) = omega(B - 1)$ in all 110,654 monic bases of degree $e >= 3$ with
  $q = 2$ and $e <= 13$, $q = 3$ and $e <= 8$, $q = 5$ and $e <= 6$, $q = 7$
  and $e <= 5$, $q = 11$ and $e = 4$, $q = 13$ and $e <= 4$; in 379,700 polynomials of the
  factor types with no good factor, up to $e = 22$ for $q = 2$; and in
  random samples of the first open type.
]

#conjecture(id: "worlds-ff-kB-conj", title: [$k(B) = omega(B - 1)$], src: "29.2")[
  $k(B) = omega(B - 1)$ for every base $B$.
]

An exception needs a squarefree $B - 1$ with no good factor, no factor of
degree 2, and $q >= e - 1$. The first such case is $e = 11$, with factors of
degrees 5 and 6 and $q >= 11$ (#q(111)).

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

=== A model that keeps the blocks

The heuristic suggests a better model: keep the Frobenius blocks exactly
and randomize only what they do not fix. By @worlds-ff-blocks, $F(x)$ is
assembled from $e$ generating digits $p_0, dots, p_(e-1)$, with
$p_(e-1) = D_(e-1)$ and $p_j = sigma(p_(j+1)) + D_j$, where $sigma$ is a
fixed map on digits (#lib("24.2"), Corollary 24.3). The digit $p_j$ fills
the positions from $q^(j-1)$ to $q^j - 1$ through its block. So the class
sums of $F(x)$ are the class of $p_0$ plus one fixed function $K_j (p_j)$ for
each $j >= 1$, and $x |-> (p_0, dots, p_(e-1))$ is a bijection.

#definition(id: "worlds-ff-blockmodel", title: "Block model", src: "29.4")[
  Keep the maps $K_j$, and replace each generating digit $p_j$ by a uniform
  digit of the same degree (zero stays zero). In the refined block model
  the random digits must also give the same value of $F$ modulo $B - 1$ as
  the true ones.
]

The refined block model needs no $kappa(B)$: the larger kernel of
@worlds-ff-generic is built in, because the generic sector keeps its
degrees. A model solution also satisfies the identity modulo $B - 1$, as a
true solution does. The expected count is an exact finite sum, which takes
seconds per base orbit.

#computation(id: "worlds-ff-blockcomp", title: "The block model against the census", src: "29.4")[
  Mean number of solutions per base under $0^0 = 0$:
  #align(center, btable(
    columns: 5,
    align: (left, right, right, right, right),
    [$(q, e)$], [census], [refined model], [refined block model], [Pearson, per orbit],
    [$(5, 3)$], [34.4], [26.2], [31.6], [26.5 to 6.6 (25 orbits)],
    [$(7, 3)$], [76.3], [64.8], [73.5], [48.5 to 13.8 (63)],
    [$(5, 4)$], [60.5], [45.4], [58.7], [749 to 187 (160)],
  ))
  The block model comes within 17% of the census in 16 of the 21 factor
  types of $B - 1$, against 5 of 21 for the refined model. The irreducible
  quartic of $(5, 4)$ gets 8.8 against a census of 10.0; the refined model
  gives 4.9.
]

#heuristic(id: "worlds-ff-blockverdict", title: "Keep the forcing in full", src: "29.4")[
  Keeping all $e$ generating digits and their degrees, and randomizing the
  rest, explains most of the $FF_q [T]$ gap: the total error drops from 18%
  to 33% down to 3% to 9%, and the misfit per orbit by a factor of 4. Keeping
  only the top digit is not enough. The types with a repeated factor of
  $B - 1$ still miss: two double roots in $(5, 4)$ have 2.09 times the block
  model, and two types without solutions get 5 and 6 from the model.
]

For a repeated factor the ring $R$ has a nilradical, where the identity
behaves differently, as in part 3 of @worlds-ff-kB (#q(115)). The recipe
"keep the forced digits, randomize the rest" is the same one that the
forced top digits apply in the integers (@sec-model-defects). The next
section applies it to the factorial system.

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
Zero against 4.5 has probability 0.011. Near-solutions show that the model
itself is wrong here: with offsets $D = 1, dots, 100$ there are none for
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
larger than Poisson.

=== A model with the top digits kept

The fix that works in $FF_q [T]$ also works here: keep the true top digits
of $F$ and randomize the rest. For a multiset $c$ whose sum $F(c)$ lies in
the window $[L!, (L + 1)!)$, let $T$ be the top $K$ factorial digits of
$F(c)$. Treat only the digits at positions 1 to $L - K$ as random. The
chance that the digits of $F(c)$ form $c$ is then
$ bb(1)(T subset c) dot A(c - T, L - K) / (product_(i <= L - K) (i + 1)), $
where $A(c, N)$ counts the ways to place a multiset of $N$ digits at the
positions 1 to $N$ with each value $u$ only at a position $>= u$. These
placements form a Ferrers board, so $A$ is a product of binomial
coefficients: place the values from the largest down, each into the free
positions at or above it.

#proposition(id: "worlds-fact-topmodel", title: "The top-digit model", src: "29.5")[
  Let $n$ be uniform in the window, $W = [L!, (L + 1)!)$. Summed over all
  multisets, the top-$K$ model expects
  $ E_L (K) = E_n [bb(1)(F(n) in W) dot r(n)] $
  solutions of length $L$. Here $c(n)$ is the multiset of $n$, $T$ is the
  top $K$ digits of $F(n)$, and $r(n)$ is the chance that a random
  arrangement of $c(n)$ has the top digits $T$, divided by the chance that a
  uniform member of $W$ has them. $E_L (0)$ is the plain model and
  $E_L (L)$ is the exact number of solutions in $W$.
]
#proof[
  The plain model is the sum over multisets $c$ with $F(c) in W$ of the
  number of arrangements of $c$ in $W$, divided by $|W|$. So a sum over
  multisets is an expectation over $n$, with weight $|W|$ over the number of
  arrangements of $c(n)$. The ratio of $A(c - T, L - K)$ to the number of
  arrangements is the chance that a random arrangement has top digits $T$,
  and $|W|$ over the product is the inverse of the second chance. For $K = L$ the
  indicator says that the digits of $F(c)$ are $c$.
]

The adaptive version keeps the positions where the largest digit $v$ of $n$
can sit, $K = L - v + 1$: the forcing of @worlds-fact-failure. Call a
length $L$ open if this model expects more than 0.01 solutions.

#computation(id: "worlds-fact-open", title: "Open lengths", src: "29.5")[
  By sampling, $3 dot 10^6$ strings per length under $0^0 = 0$ and $10^6$
  under $0^0 = 1$, for $3 <= L <= 100$:
  - for $L <= 33$, under both conventions, the open lengths are 8, 10, 13,
    14, 15, 18, 19, 20, 24, 26, 28, 29, 30 and 32: 14 of 31;
  - for $34 <= L <= 100$, 11 to 14 lengths are open, among them 35 and 40;
  - among the lengths 10 to 26, all 8 closed lengths have no near-solution
    at the offsets $D = 1000 j$, where the plain model expects 81; all 5
    lengths with near-solutions are open;
  - the model expects 3.85 solutions below $34!$ under $0^0 = 0$ and 3.90
    under $0^0 = 1$, against 4.6 and 4.8 for the plain model.
]

So about half the lengths are open, not 5 of 17. The model moves the
expected solutions between lengths and hardly changes their total. Under a
Poisson law, no solution below $34!$ then has probability
$e^(-3.85) = 0.021$. But coincidences come in clusters: the offsets that
carry at least one near-solution are only 0.24 to 0.39 times the model mean,
the rest being repeats of one multiset. With this calibration the empty
census has probability 0.22 to 0.39, an ordinary outcome (heuristic).

#heuristic(id: "worlds-fact-predict", title: "Beyond 34!", src: "29.5")[
  For $34 <= L <= 40$ the top-digit model expects about 0.29 solutions, so
  at least one with probability 0.07 to 0.10 after the cluster calibration.
  The open lengths there are 35 and 40. Up to $L = 100$ it expects about
  2.5, at least one with probability 0.45 to 0.6. Beyond $L = 50$ these
  numbers are uncertain by a factor of 2.
]

A census to $L = 40$ needs integers wider than 128 bits and a few $10^8$
tree nodes per length; it has not been run. Like the plain model, the
top-digit model expects finitely many solutions, but it gives nothing a
proof could use. Whether the factorial system has finitely many solutions
is open; no size argument and no residue are available (@sec-open-list).

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
    of the weights (@worlds-prop-index). It is 2 exactly when the modulus is even and the weights
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
