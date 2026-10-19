#import "../template.typ": *

= Definitions and first facts <ch-basics>

This chapter fixes the notation and proves the facts that every later chapter
uses. Most of them are elementary. Two of them shape everything that follows.
A solution in base $b$ has at most $b$ digits, so each base has finitely many
solutions. And a fixed digit string is a solution in at most one base, so short
solutions can be found for all bases at once.

== The problem <sec-basics-def>

Fix a base $b >= 2$. A number $n$ with $k$ digits has the base-$b$
representation
$ n = s_(k-1) b^(k-1) + dots + s_1 b + s_0, quad 0 <= s_i <= b - 1, quad s_(k-1) != 0. $
Position $i$ holds the digit $s_i$, and position 0 is the last digit. We write
the digit string most significant digit first, as $(s_(k-1), dots, s_1, s_0)$,
and we write each digit in decimal. So $(3, 4, 3, 5)$ is the number 3435 in base
10, and $(3, 3)$ in base 17 is $3 dot 17 + 3 = 54$.

#definition(id: "basics-def", title: "Munchausen number")[
  Let $m in {0, 1}$ be the value given to $0^0$. The _weight_ of a digit is
  $ w(x) = x^x "for" x >= 1, quad w(0) = m. $
  The _Munchausen sum_ of $n$ is $F(n) = sum_i w(s_i)$, the sum of the weights
  of its base-$b$ digits. A _Munchausen number_ in base $b$ is a number with
  $F(n) = n$. The numbers 1 (in both conventions) and 0 (under $0^0 = 0$) are
  the _trivial_ solutions. In this document a _solution_ means a nontrivial
  one, so it has at least two digits.
]

Three examples show the flavour.

- Base 10: $3435 = 3^3 + 4^4 + 3^3 + 5^5 = 27 + 256 + 27 + 3125$. It is the
  only solution in base 10 under $0^0 = 1$. Under $0^0 = 0$ base 10 has one
  more, $438579088 = 4^4 + 3^3 + 8^8 + 5^5 + 7^7 + 9^9 + 0 + 8^8 + 8^8$.
- Base 17: $54 = (3, 3)$ and $3^3 + 3^3 = 54$.
- Base 3: $(1, 2) = 5 = 1^1 + 2^2$ and $(2, 2) = 8 = 2^2 + 2^2$.

We write $F_0$ and $F_1$ for the sum under $0^0 = 0$ and $0^0 = 1$, and
$N_m (b)$ for the number of solutions in base $b$ under the convention $m$.
$N_(m,k)(b)$ counts those with exactly $k$ digits. For a digit string, $c_x$
is the number of times the digit $x$ occurs; the vector $c = (c_0, dots,
c_(b-1))$ is the _digit multiset_. The sum $F$ depends only on the multiset,
not on the order of the digits. This simple fact is the reason why a search
can run over multisets instead of numbers (@ch-search).

#remark(id: "basics-why-both")[
  The value of $0^0$ has no agreed meaning here. Throwing away every number
  with a digit 0 discards too much, and neither convention is more natural
  than the other. So the library keeps both, and so does this document. A
  number without the digit 0 is a solution under both conventions or under
  neither (@thm-conventions). The two conventions behave differently in
  interesting ways: $0^0 = 0$ admits large algebraic families, and $0^0 = 1$
  is much more rigid.
]

== How long a solution can be <sec-basics-length>

A number with $k$ digits is at least $b^(k-1)$, while its Munchausen sum is at
most $k (b - 1)^(b - 1)$. The first grows exponentially in $k$, the second
linearly. So long numbers cannot be solutions.

#proposition(id: "thm-length", title: "Length bound", src: "1.2")[
  A solution in base $b$ has at most $b$ digits. In particular every base has
  finitely many solutions, and a solution is at most $b (b-1)^(b-1)$.
]
#proof[
  Let $n$ have $k$ digits. Then $n >= b^(k-1)$ and $F(n) <= k (b-1)^(b-1)$. For
  $k = b + 1$,
  $ ((b+1)(b-1)^(b-1)) / b^b = (1 + 1/b)(1 - 1/b)^(b-1) = (1 - 1/b^2)(1 - 1/b)^(b-2) < 1. $
  So $F(n) < b^b <= n$. Going from $k$ to $k + 1$ multiplies the bound
  $k (b-1)^(b-1)$ by $(k+1) slash k < 2 <= b$ and the lower bound $b^(k-1)$ by
  $b$. So the inequality $F(n) < n$ persists for every $k >= b + 1$.
]

#example(id: "basics-small-bases")[
  In base 2 the only digits are 0 and 1, both of weight at most 1, so
  $F(n) <= k$ while $n >= 2^(k-1)$. The only solution is $(1, 0) = 2$ under
  $0^0 = 1$. In base 10 a solution has at most 10 digits and is below
  $10 dot 9^9 approx 3.9 dot 10^9$. In base 100 it has at most 100 digits, and
  the search space is about $4^(100)$ digit multisets. This is why base 100 is
  still out of reach (@sec-search-base100).
]

Van Berkel proved the weaker bound $n < 2 b^b$ @vanberkel2009, and Kure\u{161}
proved the bound of @thm-length @kures2021. The bound is sharp in the sense
that solutions with exactly $b$ digits exist: base 15 and base 16 each have
one under $0^0 = 0$ (@sec-basics-leading).

For short solutions a second bound is more useful. A single digit $x$ already
contributes $x^x$ to $F(n) = n$.

#proposition(id: "thm-digit-bound", title: "Digit bound", src: "1.2")[
  A $k$-digit solution in base $b$ uses only digits $x$ with $x^x < b^k$.
]

Write $X_k (b)$ for the largest such digit. Taking logarithms in
$x ln x approx k ln b$ gives
$ X_k (b) tilde (k ln b) / ln(k ln b) quad (b -> infinity, k "fixed"). $
So a solution with a fixed number of digits uses only small digits, of the
order of $ln b slash ln ln b$. This is what makes short solutions cheap to find, and it is
behind every finiteness argument for short solutions in @ch-short.

== One base per digit string <sec-basics-polynomial>

Fix a digit string $s = (s_(k-1), dots, s_0)$ instead of a number. Its value in
base $r$ is the _value polynomial_
$ P_s (r) = s_(k-1) r^(k-1) + dots + s_1 r + s_0, $
and its Munchausen sum $F(s) = sum_i w(s_i)$ does not depend on the base at all.

#definition(id: "basics-poly", title: "Munchausen polynomial")[
  The _Munchausen polynomial_ of a digit string $s$ is
  $ Q_s (r) = P_s (r) - F(s). $
  It has integer coefficients and degree $k - 1$. The string $s$ is a solution
  in base $b$ exactly when $Q_s (b) = 0$ and $b$ exceeds every digit of $s$.
]

#proposition(id: "thm-one-base", title: "One base per string", src: "1.4")[
  A digit string with at least two digits is a solution in at most one base.
]
#proof[
  The leading digit is at least 1, so $P_s (r)$ is strictly increasing for
  $r > 0$. The constant $F(s)$ is fixed. So $P_s (r) = F(s)$ has at most one
  positive root.
]

This turns the search around. Instead of fixing the base and looking for
digit strings, one can fix the digits and solve for the base. By
@thm-digit-bound the digits of a $k$-digit solution are at most $X_k (b)$, so
enumerating all strings with digits up to $M$ finds every $k$-digit solution in
every base $b$ with $b^k <= (M+1)^(M+1)$. For three digits and $M = 80$ this
covers all bases up to $10^(51.5)$ with half a million strings.
@ch-short treats $Q_s$ as an algebraic object: its roots modulo primes, its
Galois group, and its roots that are not ordinary bases.

== The two conventions for $0^0$ <sec-basics-conventions>

#proposition(id: "thm-conventions", title: "The two conventions", src: "1.5")[
  $F_1(n) = F_0(n) + z(n)$, where $z(n)$ is the number of zero digits of $n$.
  So a number without the digit 0 is a solution under both conventions or
  under neither, and a number with a zero is a solution under at most one.
]

The solutions without a zero are called _shared_. In bases 10 to 41, 35 of
the 56 solutions under $0^0 = 1$ are shared, and this makes the two counts
$N_0 (b)$ and $N_1 (b)$ correlated (@sec-model-poisson).

== Balance <sec-basics-balance>

Rewrite $F(n) = n$ as a sum over positions:
$ sum_i (s_i b^i - w(s_i)) = 0. $
The term $beta(x, i) = x b^i - w(x)$ is the _balance_ of the digit $x$ at
position $i$. A number is a solution exactly when the balances of its
placements add up to zero. Most placements have a large balance of either
sign. A few have balance zero on their own.

#tablefig(caption: [Placements with balance zero (#lib("1.3")).], id: "tab-basics-zero-balance")[
  #btable(
    columns: 2,
    align: (left, left),
    [placement], [why its balance is zero],
    [a 0 anywhere, under $0^0 = 0$], [$0 dot b^i - 0 = 0$],
    [a 1 at position 0], [$1 - 1^1 = 0$],
    [a digit $a$ at position $i >= 1$ with $a^(a-1) = b^i$], [$a dot b^i = a^a$],
  )
]

A digit of the third kind is called _self-paying_: it adds the same amount to
$n$ and to $F(n)$. @ch-constructions builds solutions out of these
placements. The point of view also explains why $0^0 = 0$ is the richer
convention. Under $0^0 = 0$ zeros are free, so zero-balance placements can be
combined at will. Under $0^0 = 1$ each zero costs 1, and something else in the
number must pay for it.

== The digit-sum identity and other congruences <sec-basics-congruences>

Every integer is congruent to its digit sum modulo $b - 1$, because
$b equiv 1 med (mod b - 1)$. For a solution, $n = F(n)$, and the digit sum of
$n$ is $sum_x x c_x$. This gives a condition on the multiset alone.

#proposition(id: "thm-digit-sum", title: "Digit-sum identity", src: "1.6")[
  Every solution satisfies
  $ sum_x c_x (w(x) - x) equiv 0 med (mod b - 1), $
  that is, the sum of $w(x) - x$ over its digits is divisible by $b - 1$.
]

#example(id: "basics-identity-3435")[
  For 3435 in base 10 the terms are $3^3 - 3 = 24$, $4^4 - 4 = 252$, $24$
  again and $5^5 - 5 = 3120$. Their sum is $3420 = 9 dot 380$, divisible by
  $b - 1 = 9$ as it must be. A random multiset meets the identity with
  probability about $1 slash (b - 1)$, so the identity alone removes most
  candidates. In odd bases under $0^0 = 0$ it holds about twice as often, as
  rule (2) below shows.
]

The parts of this identity modulo the prime powers dividing $b - 1$ give
simple rules. The basic fact is that $x^x equiv x med (mod 2)$ for every
$x >= 1$, since $x^x$ and $x$ have the same parity.

#proposition(id: "basics-parity-rules", title: "Rules from the identity", src: "1.6")[
  Let $n$ be a solution in base $b$.
  + If $b$ is odd and $0^0 = 1$, then $n$ has an even number of zeros.
  + If $b$ is odd and $0^0 = 0$, the identity holds modulo 2 for every
    multiset.
  + If $b equiv 1 med (mod 4)$ and $0^0 = 0$, the number of digits
    $x equiv 2 med (mod 4)$ is even.
  + If $b equiv 1 med (mod 3)$ and $0^0 = 0$, the number of digits
    $x equiv 2 med (mod 6)$ is a multiple of 3.
  + If $b$ is even, the last digit of $n$ is odd exactly when $n$ has an odd
    number of odd digits; under $0^0 = 1$, count the zeros together with the
    odd digits.
]
#proof[
  (1) and (2): modulo 2 every term $w(x) - x$ with $x >= 1$ vanishes, and a
  zero contributes $m$. So the identity modulo 2 reads $m c_0 equiv 0$.

  (3): modulo 4, $x^x equiv x$ for odd $x$ (since $x^2 equiv 1 med (mod 8)$
  and $x - 1$ is even) and for $x equiv 0 med (mod 4)$. For $x equiv 2 med
  (mod 4)$, $x^x equiv 0$ while $x equiv 2$. So the sum is $2 c$ modulo 4,
  where $c$ counts the digits $equiv 2 med (mod 4)$.

  (4): modulo 3, $x^x equiv x$ unless $x equiv 2 med (mod 3)$ and $x$ is even,
  that is $x equiv 2 med (mod 6)$; then $x^x equiv (-1)^x = 1$ and
  $w(x) - x equiv -1$. So the sum is $-c$ modulo 3.

  (5): in an even base $n equiv s_0 med (mod 2)$, and
  $F(n) equiv sum_i s_i^(s_i) equiv$ (number of odd digits) $+ m z(n)$.
]

The catalog of all known solutions obeys every rule, as it must. Rule (2) is
the most important one: under $0^0 = 0$ a random multiset in an odd base meets
the identity modulo 2 for free. @ch-model shows that this doubles the
expected number of solutions in odd bases.

Can a cleverer congruence say more? The identity uses one residue of $n$ that
the digit multiset determines. There are no others.

#proposition(id: "thm-only-residue", title: "The only invariant residue", src: "10.4")[
  If $n mod M$ depends only on the digit multiset of $n$ for all $n$ with at
  least two digits, then $M$ divides $b - 1$.
]
#proof[
  Take a number whose last two digits are $x$ and $y = x - 1$, and swap them.
  The multiset is unchanged, and the value changes by
  $(x - y) b + (y - x) = b - 1$. So $M$ divides $b - 1$.
]

A related question asks for congruences that the map $n |-> F(n)$ itself
preserves. Here there is exactly one case.

#theorem(id: "thm-parity-invariant", title: "Parity invariant", src: "15.1")[
  Let $b >= 3$ and $q >= 2$. Then $F(n) equiv n med (mod q)$ for every
  $n >= 1$ if and only if $q = 2$, $b$ is odd and $0^0 = 0$.
]
#proof[
  Suppose the congruence holds for all $n$. The number $n = b + 1$ has digits
  $(1, 1)$, so $2 equiv b + 1$ and $b equiv 1 med (mod q)$. The number $n = b$
  has digits $(1, 0)$, so $1 + m equiv b equiv 1$, which forces $m = 0$. The
  digit 2 exists because $b >= 3$, and $n = 2$ gives $4 equiv 2$, so $q = 2$,
  and then $b$ is odd. Conversely, for odd $b$ every $n$ is congruent modulo 2
  to its digit sum, and $x^x equiv x med (mod 2)$ with $w(0) = 0$. So
  $F(n) equiv n med (mod 2)$.
]

So in an odd base under $0^0 = 0$ the even numbers and the odd numbers are two
sets that $F$ maps into themselves. This has consequences for the cycles of
$n |-> F(n)$ (@sec-model-cycles).

== Leading digits and solutions with $b$ digits <sec-basics-leading>

The largest digits of a number supply almost all of its Munchausen sum, so
they decide its length and its leading digit. The leading digit of a $k$-digit
solution is $floor(F(n) slash b^(k-1))$. In bases 20 to 38, for all 26
solutions under $0^0 = 1$, the two largest digit values alone give the leading
digit.

The largest digit $b - 1$ weighs
$ (b - 1)^(b-1) = b^(b-1) (1 - 1/b)^(b-1) approx b^(b-1) / e. $
So $c$ copies of $b - 1$ contribute about $(c slash e) b^(b-1)$. Since
$(1 - 1/b)^(b-1) > 1/e$, three copies already exceed $b^(b-1)$. A solution with
$b - 1$ digits therefore contains the digit $b - 1$ at most twice. One copy
puts its leading digit near $b slash e$, and two copies near $2b slash e$.

#proposition(id: "basics-bdigit", title: [Solutions with $b$ digits], src: "1.8")[
  For $b >= 7$, a $b$-digit solution contains the digit $b - 1$ at least three
  times.
]
#proof[
  If $b - 1$ occurs at most twice, then
  $F(n) <= 2 (b-1)^(b-1) + b (b-2)^(b-2)$. Divided by $b^(b-1)$ this is
  $2 (1 - 1/b)^(b-1) + (1 - 2/b)^(b-2)$. Both terms decrease as $b$ grows, and
  at $b = 7$ the sum is 0.979. So $F(n) < b^(b-1) <= n$.
]

With three to five copies of $b - 1$ the sum is about $(c slash e) b^(b-1)$,
between $1.1$ and $1.9$ times $b^(b-1)$, so the leading digit of a $b$-digit
solution is 1. Both known $b$-digit solutions fit this description exactly.

#computation(id: "basics-bdigit-known", title: [Solutions with $b$ digits], src: ("7.1", "8.6"))[
  Under $0^0 = 0$, base 15 has the $b$-digit solution
  $(1, 2, 4, 3, 14, 14, 13, 3, 4, 1, 9, 1, 1, 0, 14)$ and base 16 has
  $(1, 2, 3, 11, 2, 3, 0, 9, 15, 15, 5, 7, 2, 15, 6, 11)$. Both start with 1 and
  contain $b - 1$ exactly three times. No other base from 3 to 45 has a
  $b$-digit solution under $0^0 = 0$, and none of them has one under
  $0^0 = 1$.
]

The original conjecture was that no base $b > 2$ has a $b$-digit solution. The
two examples refute it under $0^0 = 0$. Under $0^0 = 1$ it remains open.
The probabilistic model of @ch-model at first expected a $b$-digit solution in
about 8% of large bases, so the empty range 3 to 45 looked suspicious. A finer
look (@sec-model-defects) shows that the model overestimates this length at
these sizes, because the forced top digits of a $b$-digit sum use up copies of
large digits. With that correction the absence is an ordinary event, with
probability about 0.27.

== The data at a glance <sec-basics-data>

The exhaustive search of @ch-search has found every solution in every base
from 2 to 41, and in base 43, under both conventions. @tab-basics-counts gives
the counts. The full lists are in @app-tables.

#let counts = csv("../data/counts-by-base.csv").slice(1)
#let half = calc.ceil(counts.len() / 2)
#let count-cells(rows) = rows.map(r => (
  [#r.at(0)], [#r.at(1)], [#r.at(2)], [#r.at(3)], [#r.at(4)],
)).flatten()

#tablefig(
  caption: [Nontrivial solutions per base. $N_0$ and $N_1$ count solutions
  under $0^0 = 0$ and $0^0 = 1$; "shared" counts the zero-free solutions,
  which belong to both; "longest" is the largest number of digits under
  either convention. Computed exhaustively (#lib("4.2")).],
  id: "tab-basics-counts",
)[
  #block(breakable: false, grid(
    columns: 2,
    column-gutter: 1.2em,
    btable(
      columns: 5,
      align: (right, right, right, right, right),
      [base], [$N_0$], [$N_1$], [shared], [longest],
      ..count-cells(counts.slice(0, half)),
    ),
    btable(
      columns: 5,
      align: (right, right, right, right, right),
      [base], [$N_0$], [$N_1$], [shared], [longest],
      ..count-cells(counts.slice(half)),
    ),
  ))
]

A few features stand out, and later chapters explain them.

- The counts are small and irregular: zero to seven per base. The
  probabilistic model of @ch-model predicts about one solution per base and
  convention on average, with Poisson fluctuations, and about twice as many
  in odd bases under $0^0 = 0$.
- The longest solution usually has $b - 1$ digits. That is the model's most
  likely length.
- Bases 19, 27 and 35 have no solution under either convention. They are the
  only such bases from 3 to 43. The model expects roughly one base in eight
  to be empty (@sec-model-empty).
- Perfect powers stand out under $0^0 = 0$. Base 25 has five solutions and
  base 32 has four. They come from self-paying digits (@ch-constructions).

Bases beyond 43 are expensive: each base costs about 1.9 times the previous
one. Base 44 was searched with an inexact rule that can miss solutions
(@sec-search-inexact). Under $0^0 = 1$ it found one solution with 43 digits,

#pad(x: 2em)[(32, 32, 36, 30, 0, 0, 37, 23, 32, 33, 4, 5, 17, 4, 30, 7, 31, 25,
43, 25, 15, 21, 38, 19, 18, 7, 35, 10, 34, 39, 4, 30, 25, 33, 24, 43, 27, 26,
13, 1, 38, 24, 22),]

and none under $0^0 = 0$. A search of bases 39 to 127 restricted to numbers
with at most 30 digits adds the short solutions of those bases, such as
$(3, 8, 6, 2, 0)$ in base 48 and $(6, 1, 5)$ in base 91.

== Earlier work <sec-basics-history>

Munchausen numbers belong to a family of recreational problems about digits.
The best known relatives are the _narcissistic numbers_, equal to the sum of
their digits raised to the number of digits, such as
$153 = 1^3 + 5^3 + 3^3$ @oeis-a005188, and the _factorions_, equal to the sum
of the factorials of their digits, such as $145 = 1! + 4! + 5!$
@oeis-a014080 @oeis-a193163. Both appear again in @ch-worlds as test cases for
the probabilistic model.

For Munchausen numbers themselves the published record is short.

- OEIS A166623 @oeis-a166623 lists the solutions under $0^0 = 1$ for bases 2
  to 35. The table comes from one search by Karl W. Heuer in 2011, with an
  unpublished method. The library's search agrees with it in every base.
  For $0^0 = 0$ no published list beyond about base 17 was found, and no
  published search of bases 36 to 41 under either convention.
- Van Berkel @vanberkel2009 studied 3435 and proved that a solution is below
  $2 b^b$.
- Kure\u{161} @kures2021 proved the length bound of @thm-length and described the
  two-digit family $(1, c)$ of @sec-cons-two-digit.
- Knuth's program back-pdi @knuth-backpdi searches for decimal perfect
  digital invariants. It uses the same leading-digit bounds as the search of
  @ch-search, with exact pruning.

Almost everything else in this document comes from the library in
`docs/library`, built by a long series of computations and arguments. Each
statement carries a pointer such as #lib("8.3") to the section of the library
where its proof, its computation or its data can be found.

=== A map of this document

The chapters are organized by theme, not by the order of discovery.

- @ch-constructions collects the solutions that follow from identities:
  twins, self-paying digits, swaps, the two-digit families, and the binomial
  families that give infinitely many solutions of every length.
- @ch-model presents the probabilistic model. It treats a solution as a
  coincidence and predicts the counts, the lengths and the parity effect.
- @ch-search describes the exhaustive search, its cost, faster searches that
  accept a small miss rate, and the complexity barriers.
- @ch-short treats short solutions through the Munchausen polynomial: local
  obstructions, coverings, Galois groups, and a heuristic for integer roots.
- @ch-diophantine studies the exponential equation $b(b + x) = x^n + c$ behind
  the three-digit solutions $(1, x, 1)$, such as $(1, 7, 1)$ in base 904.
- @ch-worlds moves the problem to other number systems and other weights,
  and asks what is universal.
- @ch-open lists the open problems.

The appendices give short primers on the tools that go beyond a first course,
tables of all known solutions, a description of the software and data, and an
index of every result with its status.
