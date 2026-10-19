#import "../template.typ": *

= Constructions and families <ch-constructions>

Most solutions in large bases look random, and @ch-model treats them as
coincidences. This chapter is about the ones that do not look random: families
that follow from an identity between powers and need no search. They explain
why some bases have many solutions, why every length occurs, and why some
integers are solutions in many bases at once. They also include the most
surprising result of the library, the binomial families of
@sec-cons-binomial, which give infinitely many solutions of every length
under $0^0 = 1$.

All the constructions below were checked with exact integer arithmetic
(`analysis/verify_constructions.py` and the scripts named in each library
section), and the exhaustive searches find exactly the predicted members in
their ranges.

== Twins <sec-cons-twins>

The simplest construction changes one digit.

#proposition(id: "thm-twins", title: "Twins", src: "2.1")[
  Under $0^0 = 0$, a number $n$ whose last digit is 0 is a solution if and
  only if $n + 1$ is a solution.
]
#proof[
  The number $n + 1$ has the digits of $n$ with the final 0 replaced by a 1.
  So $F(n + 1) = F(n) + 1$.
]

So under $0^0 = 0$ every solution that ends in 0 or 1 has a twin. Bases 2 to
41 contain 8 twin pairs, for example $(4, 0, 0)$ and $(4, 0, 1)$ in base 8,
where $4 dot 64 = 256 = 4^4$. Under $0^0 = 1$ there are no twins: a final 0
and a final 1 both weigh 1, so $n$ and $n + 1$ have the same sum and cannot
both equal it.

== Self-paying digits <sec-cons-selfpaying>

A digit $a >= 2$ at a position $k >= 1$ is _self-paying_ if
$a b^k = a^a$, that is $a^(a-1) = b^k$. Its balance is zero
(@sec-basics-balance): it adds the same amount to $n$ and to $F(n)$. The base
64 is the standard example: $4 dot 64 = 4^4$ and $16 dot 64^(10) = 2^(64) =
16^(16)$, so the digit 4 pays for itself at position 1 and the digit 16 at
position 10.

#proposition(id: "thm-self-paying", title: "Which digits pay for themselves", src: "2.2")[
  Write $b = r^t$ with $r$ not a perfect power. The self-paying digits of base
  $b$ are the digits $a = r^s$ with $1 <= s < t$ and $t divides s(r^s - 1)$,
  at position $k = s(r^s - 1) slash t$. In particular only perfect powers have
  self-paying digits.
]
#proof[
  If $a^(a-1) = b^k$, then $a$ and $b$ are multiplicatively dependent, so both
  are powers of one integer. Since $r$ is not a perfect power, $b = r^t$ and
  $a = r^s$ for some $s$. The equation becomes $r^(s(r^s - 1)) = r^(t k)$, that
  is $s(r^s - 1) = t k$, and $a < b$ means $s < t$.
]

Every odd square $r^2$ has one: the digit $r$ at position $(r - 1) slash 2$,
because $r dot r^(r-1) = r^r$. Some perfect powers have none, for example
4, 16, 27, 36 and 100. The next statement says exactly which.

#proposition(id: "cons-sp-char", title: "Bases with a self-paying digit", src: "15.3")[
  Write $b = r^t$ with $r$ not a perfect power. Base $b$ has a self-paying
  digit if and only if $t$ has a prime factor that does not divide $r$.
]
#proof[
  Write $t = U V$, where $V$ collects the prime powers of $t$ whose primes
  divide $r$, and $U$ the rest. Since $r^s - 1$ is prime to $r$, the condition
  $t divides s(r^s - 1)$ forces $V divides s$. If $U = 1$, this means
  $t divides s$, impossible for $1 <= s < t$. If $U > 1$, take
  $s = V dot "ord"_U (r)$, where $"ord"_U (r)$ is the multiplicative order of
  $r$ modulo $U$. Then $U divides r^s - 1$ and $V divides s$, so
  $t divides s(r^s - 1)$, and $s <= V phi(U) < U V = t$.
]

So every base $r^p$ with $p$ prime and $p$ not dividing $r$ has a self-paying
digit, while $4 = 2^2$, $16 = 2^4$, $27 = 3^3$, $36 = 6^2$ and $100 = 10^2$ do
not. There are 47 bases up to 4096 with at least one self-paying digit
(`analysis/selfpaying.py`). A base can have several, but they are spread out.

#proposition(id: "cons-sp-spacing", title: "Self-paying digits are far apart", src: "8.3")[
  If $r^s$ and $r^u$ with $s < u$ are self-paying digits of base $b = r^t$, at
  positions $k_s$ and $k_u$, then $k_u > r k_s >= 2 k_s$. So base $b$ has fewer
  than $log_2 b$ self-paying digits, and no two of them sit at adjacent
  positions.
]
#proof[
  By @thm-self-paying, $k_u slash k_s = u(r^u - 1) slash (s(r^s - 1))$. With
  $u >= s + 1$ this is at least $(r^(s+1) - 1) slash (r^s - 1) > r$. The
  digits are $r^s$ with $s < t = log_r b <= log_2 b$.
]

Under $0^0 = 0$ self-paying digits combine freely with any solution, because
the zeros around them cost nothing.

#proposition(id: "thm-structure-m0", title: [Structure under $0^0 = 0$], src: "2.2")[
  Under $0^0 = 0$, setting a self-paying digit to 0 turns a solution into a
  solution, and so does putting a self-paying digit on a position that holds
  0. Every solution splits uniquely into
  - a _core_: a solution, or 0, with no self-paying digit and with a last digit
    other than 1;
  - a set of self-paying digits on positions where the core has a 0;
  - optionally a final 1, if the core ends in 0.
  Every such combination is a solution.
]
#proof[
  Each operation adds or removes one placement of balance zero, so it keeps
  the total balance at zero. The core is what remains after removing all
  self-paying digits and a final 1.
]

#corollary(id: "cons-sp-count", title: "Solutions from self-paying digits", src: "2.2")[
  If base $b$ has $C$ self-paying digits, then $N_0 (b) >= 2^(C+1) - 2$.
]
#proof[
  Take the core 0, any subset of the self-paying digits and an optional final
  1, and leave out the two trivial solutions 0 and 1.
]

Under $0^0 = 1$ a zero weighs 1, so removing a self-paying digit leaves a
number whose sum is too large by one. Self-paying digits still help when they
sit directly above a solution of the right length.

#proposition(id: "cons-sp-top", title: "A self-paying digit on top", src: "2.2")[
  Let $a$ be self-paying at position $k$ in base $b$, and let $n' < b^k$ have
  $p$ zeros between its leading digit and position $k$. Then $a b^k + n'$ is a
  solution if and only if $F(n') + p w(0) = n'$.
]

#example(id: "cons-sp-examples")[
  $(3, 1)$ in base 9 is the self-paying 3 at position 1 above the trivial
  solution 1. $(5, 1, 3)$ in base 25 is the self-paying 5 at position 2
  ($5 dot 25^2 = 5^5$) above the 2-digit solution $(1, 3)$ of base 25, since
  $25 + 3 = 1 + 3^3$. Both are solutions under either convention.
]

== Swaps and chains <sec-cons-swaps>

Two digits can also pay for each other. Put a digit $a$ at position $k$ and
the digit $c = a^a$ at position 0. If $a b^k = c^c$, then the value of each
digit equals the weight of the other: $a b^k = w(c)$ and $c = w(a)$. With
zeros in between and $0^0 = 0$, the number $(a, 0, dots, 0, a^a)$ is a
solution. The condition is
$ b^k = a^(a^(a+1) - 1) quad "and" quad a^a < b. $

#example(id: "cons-swap-examples", title: "Swaps")[
  - $a = 2$, $k = 1$: $(2, 4)$ in base 128, since $2 dot 128 = 2^8 = 4^4$.
  - $a = 3$: $b^k = 3^(80)$, so $(3, 0, dots, 0, 27)$ is a solution in the
    bases 81, 243, $3^8$, $3^(10)$, $3^(16)$, $3^(20)$, $3^(40)$ and
    $3^(80)$. In base $3^t$ it has $80 slash t + 1$ digits.
  - Every odd $a$ gives the 3-digit swap $(a, 0, a^a)$ in base
    $a^((a^(a+1) - 1) slash 2)$.
  - $a = 4$: $(4, 0, dots, 0, 256)$ with 187 digits in base 2048, since
    $4^(1023) = 2^(2046) = 2048^(186)$.
]

Swaps combine with self-paying digits under $0^0 = 0$. Base 81 has
$(3, 0, dots, 0, 9, 0, 0, 0, 27)$ with 21 digits: the swap of 3 and 27, and
the self-paying 9 at position 4 ($9 dot 81^4 = 3^(18) = 9^9$).

Under $0^0 = 1$ the zeros must be paid for. Base 64 has an example that uses
every mechanism at once:
$ (16, 0, 0, 0, 0, 0, 1, 0, 0, 4, 8). $
The digits 16 (position 10) and 4 (position 1) pay for themselves. The 1 at
position 4 is worth $64^4 = 2^(24) = 8^8$, the weight of the final 8. The final
8 is worth 8, which pays for the weight of the 1 and of the seven zeros. A
general construction behind this example follows.

#theorem(id: "cons-chains", title: "Chains and cycles", src: "15.5")[
  Let $b = r^t$. For $0 <= u < t$ put $phi(u) = u r^u mod t$ and
  $pi(u) = floor(u r^u slash t)$. Choose $u_0 >= 1$ and follow
  $u_(i+1) = phi(u_i)$ until $u_j = 0$. Place $c = r^(u_0)$ at position 0 and
  the digit $r^(u_(i+1))$ at position $pi(u_i)$ for $0 <= i < j$. Add any set
  of cycles $(v_1, dots, v_l)$ of $phi$ on ${1, dots, t - 1}$, with $r^(v_i)$
  at position $pi(v_(i-1))$, indices modulo $l$. If all positions differ and
  the number has exactly $c - 1$ zeros below its leading digit, it is a
  solution under $0^0 = 1$.
]
#proof[
  The digit $r^(phi(u))$ at position $pi(u)$ has the value
  $r^(phi(u) + t pi(u)) = r^(u r^u) = w(r^u)$. So each chain digit pays for the
  weight of its predecessor in the chain, and each cycle digit pays for the
  weight of the previous digit of its cycle. What is left to pay is the
  weight 1 of the last chain digit $r^0 = 1$ and the weight $c - 1$ of the
  zeros. Their sum is $c$, the value of the digit at position 0. The digits
  are below $b$ because $u < t$.
]

Cycles of length 1 are the self-paying digits, and cycles of length 2 are the
swaps. In base $64 = 2^6$ the chain $3 -> 0$ puts $c = 8$ at position 0 and
the digit 1 at position $pi(3) = floor(24 slash 6) = 4$; the fixed points
$u = 2$ and $u = 4$ of $phi$ give the self-paying 4 and 16. The family
$(a, 1)$ in base $a^(a-1)$ is the degenerate case without zeros.

#computation(id: "cons-chain-census", title: "Chain solutions", src: "15.5")[
  For all bases $r^t$ with $2 <= r <= 40$, $r$ not a perfect power, and
  $2 <= t <= 300$, the construction of @cons-chains gives 43 solutions. 42 of
  them are $(a, 1)$ in base $a^(a-1)$, and the other one is the 11-digit
  solution of base 64. No base gets more than 2.
]

Swaps also show that the cores of @thm-structure-m0 can sit in bases with
self-paying digits in infinitely many ways.

#theorem(id: "cons-swap-cores", title: "Swaps are cores in self-paying bases", src: "15.3")[
  For every $a >= 2$ that is not a perfect power,
  $ (a^(a+1), 0, dots, 0, a, a^a) quad (a + 2 "digits") $
  is a solution in base $a^(a^(a+1) - 1)$ under $0^0 = 0$. For $a = 2$ it is
  $(8, 0, 2, 4)$ in base 128.
]
#sketch[
  The swap $(a, a^a)$ is a 2-digit solution in $B = a^(a^(a+1) - 1)$. The
  digit $a^(a+1)$ is self-paying at position $a + 1$, because
  $(a^(a+1))^(a^(a+1) - 1) = B^(a+1)$. Position $a + 1 >= 3$ is free, so
  @thm-structure-m0 applies.
]

== Two-digit solutions <sec-cons-two-digit>

Two-digit solutions are completely described by a divisibility condition.
Write $g(c) = w(c) - c$.

#proposition(id: "thm-two-digit", title: "Two-digit solutions", src: "2.4")[
  The string $(a, c)$ is a solution if and only if $a$ divides $g(c)$ and
  $b = (a^a + g(c)) slash a$ exceeds $a$ and $c$. The base is then $b$.
]
#proof[
  The equation $a b + c = a^a + w(c)$ solved for $b$.
]

Infinite families follow at once.

- $a = 1$: $(1, c)$ in base $c^c - c + 1$, for every $c >= 2$. For example
  $(1, 2)$ in base 3 and $(1, 3)$ in base 25. Under $0^0 = 1$ also $(1, 0)$
  in base 2.
- $a = c$: $(c, c)$ in base $2 c^(c-1) - 1$, since $c divides c^c - c$. For
  example $(2, 2)$ in base 3, $(3, 3)$ in base 17 and $(4, 4)$ in base 127.
- $c = 1$, and under $0^0 = 0$ also $c = 0$: $(a, 1)$ and $(a, 0)$ in base
  $a^(a-1)$, for every $a >= 3$. Here $a$ is self-paying.
- Any $a$ with $c equiv 0$ or $1 med (mod a)$, because then
  $a divides c^c - c$. For example $(2, c)$ in base $(c^c - c + 4) slash 2$
  for every $c >= 2$.

#computation(id: "cons-two-digit-count", title: "Two-digit solutions with small digits", src: "2.4")[
  There are 2,637 two-digit solutions with digits up to 60. Of these, 119 have
  the form $(1, c)$, 118 the form $(c, c)$, 174 end in 0 or 1, and the other
  2,226 are pairs with $a divides c^c - c$.
]

So two-digit solutions are plentiful: the condition $a divides g(c)$ holds
with probability about $1 slash a$, and $sum 1 slash a$ diverges. But each base
has very few. The next theorem, proven in #lib("15.2"), settles the question
how many.

#theorem(id: "thm-two-two-digit", title: "Two 2-digit solutions", src: "15.2")[
  Under $0^0 = 1$, base 3 is the only base with two 2-digit solutions,
  $(1, 2)$ and $(2, 2)$. Under $0^0 = 0$ the bases with two 2-digit solutions
  are base 3 and the bases $a^(a-1)$ with $a >= 3$, which have the twins
  $(a, 0)$ and $(a, 1)$. No base has three.
]
#sketch[
  Let $(a, c)$ and $(A, C)$ be solutions in base $b$:
  $a b = a^a + g(c)$ and $A b = A^A + g(C)$. If $a = A$ then $g(c) = g(C)$, and
  $g$ is injective except for $g(0) = g(1) = 0$ under $0^0 = 0$, which gives
  the twins. So let $a < A$. Then $b >= A^(A-1)$, and with $b = A^(A-1) + u$ the
  equations become $g(c) = a A^(A-1) - a^a + a u$ and $g(C) = A u$. Four
  elementary steps follow. The first equation makes $g(c)$ larger than
  $g(A - 1)$, so $c >= A$. The fast growth $g(c + 1) >= 2(c + 1) g(c)$ rules
  out $C > c$. Comparing the two equations bounds $g(c)$ below $g(A + 1)$, so
  $c = A$. Finally an inequality of the form
  $A^A (A - 2a) + A(a^a + a - A) <= 0$ leaves only $a = 1$, $A = 2$, and then
  $c = C = 2$ and $b = 3$.
]

An exact computation with $a <= 200$ and $c <= 3000$, which covers bases up to
about $10^(10400)$, confirms the statement (`analysis/dyn_two_digit.py`).

== Every length under $0^0 = 0$ <sec-cons-every-length>

Self-paying digits give solutions of every length under $0^0 = 0$.

#proposition(id: "thm-every-length-m0", title: [Every length under $0^0 = 0$], src: "2.5")[
  Under $0^0 = 0$, every length $k >= 2$ has infinitely many bases with a
  $k$-digit solution.
]
#proof[
  Take $t >= 2$, $r = t(k - 1) + 1$ and $b = r^t$. Then
  $r^(r-1) = r^(t(k-1)) = b^(k-1)$, so $r$ is self-paying at position $k - 1$,
  and $r < b$. So $(r, 0, dots, 0)$ and $(r, 0, dots, 0, 1)$ are $k$-digit
  solutions.
]

With $t = 2$ this puts a $k$-digit solution in base $(2k - 1)^2$. In the bases
up to 41 the smallest base with a $k$-digit solution under $0^0 = 0$ is
usually $k + 1$ or $k + 2$; the exceptions $k = 11$ (base 64) and $k = 21$
(base 81) are perfect powers (#lib("9.9")).

== Binomial families: every length under $0^0 = 1$ <sec-cons-binomial>

Under $0^0 = 1$ zeros cost 1 each, and the constructions above give nothing
beyond two digits. For a long time the library conjectured that each length
$k >= 3$ has only finitely many solutions under $0^0 = 1$. The evidence was
strong. Every 3-digit solution in every base up to $10^(51.5)$ is known, and
there are six. A heuristic that treats the base as the root of a random
polynomial (@sec-short-heuristic) gives a finite expected number for every
$k >= 3$. The conjecture is false. The counterexamples come from one identity,
the binomial theorem.

#theorem(id: "thm-binomial", title: "Binomial families", src: "22.3")[
  Let $j >= 2$, $c >= 1$, $e >= 1$, and put
  $ t_i = c^(j-i) binom(j, i) e^i quad (0 <= i <= j - 1), quad
    x = e^j + sum_(i=0)^(j-1) t_i^(t_i). $
  Suppose that $x^x = y^j$ for an integer $y$, that $c$ divides $y - e$, and
  that $b = (y - e) slash c$ exceeds $x$ and every $t_i$. Then
  $(t_0, dots, t_(j-1), x)$ is a $(j + 1)$-digit solution in base $b$ under
  both conventions.
]
#proof[
  The $t_i$ are the coefficients of $(c r + e)^j$ without its constant term.
  So the value of the string is
  $ P(b) = (c b + e)^j - e^j + x = y^j - e^j + x = x^x - e^j + x. $
  All digits are positive, so under both conventions
  $F = sum_i t_i^(t_i) + x^x$. The definition of $x$ says exactly that
  $P(b) = F$.
]

#corollary(id: "thm-every-length-m1", title: [Every length under $0^0 = 1$], src: "22.3")[
  For every $k >= 3$ there are infinitely many $k$-digit solutions under
  $0^0 = 1$, and under $0^0 = 0$.
]
#proof[
  Let $j = k - 1$, $c = j$ and $e = j u$ with $u >= 1$. Every $t_i$ is a
  positive multiple of $j$, since it contains the factor $c^(j-i)$ with
  $j - i >= 1$. So $t_i^(t_i) equiv 0$ and $e^j equiv 0 med (mod j)$, hence
  $j divides x$. Then $x^x = y^j$ with $y = x^(x slash j)$, and $j divides y$
  because $j divides x$, so $c = j$ divides $y - e$. Finally
  $x >= t_0^(t_0) = (j^j)^(j^j)$, so $y >= x^2$ and $b = (y - e) slash j > x$.
  Different $u$ give different digit strings.
]

For $j = 2$ the condition on $x$ is that $x$ is even or a square. With
$c = 1$ this holds for every odd $e$, and $e = 1$ gives the smallest member,
$(1, 2, 6)$ in base $6^3 - 1 = 215$: here $(b + 1)^2 = 216^2 = 6^6$. This
solution had been known for years as one of the six 3-digit solutions. Only
the family behind it was new. The next 3-digit member is short enough to
check by hand.

#example(id: "cons-46666", title: [The second member for $k = 3$])[
  Take $j = 2$, $c = 1$, $e = 3$. Then $(r + 3)^2 = r^2 + 6 r + 9$, so the
  digits are 1 and 6, and $x = 9 + 1^1 + 6^6 = 46666$. Since $x$ is even,
  $y = 46666^(23333)$ and $b = 46666^(23333) - 3$, about $10^(108942)$. In this
  base
  $ P = b^2 + 6 b + 46666 = (b + 3)^2 - 9 + 46666 = 46666^(46666) + 46657, $
  $ F = 1 + 6^6 + 46666^(46666) = 46666^(46666) + 46657. $
]

#tablefig(
  caption: [The smallest known member of the binomial family for each length,
  after $(1, 2, 6)$ in base 215 (#lib("22.3")). The search covered
  $c <= 6$ and $e <= 12$; members of other shapes may be smaller.],
  id: "tab-cons-binomial",
)[
  #btable(
    columns: 5,
    align: (right, left, left, right, right),
    [$k$], [$(c, e)$], [digits], [$x$], [base $b$],
    [3], [$(1, 3)$], [$(1, 6, x)$], [46,666], [$46666^(23333) - 3 approx 10^(108942)$],
    [4], [$(1, 2)$], [$(1, 6, 12, x)$], [8,916,100,494,921], [$x^(x slash 3) - 2 approx 10^(3.85 dot 10^(13))$],
    [5], [$(2, 2)$], [$(16, 64, 96, 64, x)$], [$approx 10^(190.3)$], [$approx 10^(10^(192.0))$],
    [6], [$(1, 4)$], [$(1, 20, 160, 640, 1280, x)$], [$approx 10^(3977)$], [$approx 10^(10^(3980))$],
    [7], [$(1, 1)$], [$(1, 6, 15, 20, 15, 6, x)$], [$approx 1.05 dot 10^(26)$], [$approx 10^(10^(26.7))$],
    [8], [$(3, 1)$], [$(2187, 5103, 5103, 2835, 945, 189, 21, x)$], [$approx 10^(18921)$], [$approx 10^(10^(18924))$],
    [9], [$(2, 2)$], [$(256, 2048, 7168, dots, 2048, x)$], [$approx 10^(76220)$], [$approx 10^(10^(76224))$],
  )
]

Why did the heuristic miss these? It treats the real root of $Q_s$ as a
random number, and asks for the chance that it is an integer. For the
binomial strings $Q_s (r) = (c r + e)^j - x^x$ exactly, so the root is an
integer whenever $x^x$ is a $j$-th power. An identity has probability one
where it holds, and the heuristic gives it weight near zero. The lists of
@sec-short-lists stay complete in their ranges, but they are not the end of
the story: the lengths 9, 18, 21, 22, 24, 26 and 28, which have no solution in
any searched base (@sec-model-window), do have solutions in astronomically
large bases.

For three digits the binomial families are the whole story of a certain
equation. Completing the square turns $p b^2 + q b + r = F$ into
$(2 p b + q)^2 = 4 p F + q^2 - 4 p r$. When one digit $x$ is large, the
dominant term of the right side is $4 p x^x$. Write the right side as
$4 p x^x + R$.

#proposition(id: "cons-r-zero", title: "When the remainder vanishes", src: "22.3")[
  Let one digit $x$ of a 3-digit string vary and fix the other two, under
  $0^0 = 1$. Then $R = 0$ only if $x$ is the last digit and
  $x = p^p + q^q + q^2 slash (4p)$. If moreover $x$ is even, then $p = c^2$ is
  a square, $q = 2 c e$, and the solutions are exactly the members of
  @thm-binomial with $j = 2$.
]

#remark(id: "cons-correction-84")[
  The library once proved finiteness for 3-digit solutions in the "square
  class", where $4 p x^x$ is a perfect square, with the other two digits at
  most 20 (#lib("8.2"), Corollary 8.4). The argument bounded $|R|$ from below
  and so silently assumed $R != 0$. @cons-r-zero shows that $R = 0$ happens
  exactly for the binomial families. With the two fixed digits at most 20
  there are 9 such strings: $(1, 2, 6)$ and eight more, $(1, 6, x)$,
  $(1, 10, x)$, $(1, 14, x)$, $(1, 18, x)$, $(4, 8, x)$, $(4, 16, x)$,
  $(9, 6, x)$ and $(9, 18, x)$, all in bases above $10^(108942)$. With these
  eight added the corollary holds. The lesson is general: a heuristic, or an
  inequality, that treats a quantity as generic must check that no identity
  makes it vanish.
]

Two near-misses of the same kind appear in the short-string data of
#lib("19.2"). The strings $(1, 0, 0, x)$ and $(1, 3, 3, x)$ with $x^x$ a cube
satisfy $P_s (b) - F(s) = x - 3$ and $x - 56$ in suitable bases, so they are
near-solutions with a fixed defect, not solutions. Whether every solution
beyond some size belongs to an identity family like these is open (#q(64)),
and so is whether $(1, 6, 46666)$ is the next 3-digit solution after
$(1, 7, 1)$ in base 904 (#q(65)).

== Self-paying blocks <sec-cons-blocks>

A self-paying digit is one placement that pays for itself. A longer string can
do the same. Split a $k$-digit string $s = (t, u)$ into a top part $t$ of $L$
digits and a tail $u$ of $m = k - L$ digits.

#lemma(id: "cons-split", title: "Splits", src: "22.1")[
  Put $R_m = b^m P_t (b) - F(t)$. Then $s = (t, u)$ is a solution in base $b$
  exactly when $R_m = F(u) - P_u (b)$. In particular $R_m = 0$ exactly when the
  tail pays for itself, $P_u (b) = F(u)$, where leading zeros of $u$ weigh
  $w(0)$.
]
#proof[
  $P_s (b) = b^m P_t (b) + P_u (b)$ and $F(s) = F(t) + F(u)$.
]

#definition(id: "cons-block-def", title: "Self-paying block", src: "22.2")[
  A _self-paying block_ is a triple $(t, b, m)$: a string
  $t = (t_1, dots, t_L)$ with $t_1 >= 1$ and $t_L >= 1$, a shift $m >= 1$ and
  a base $b > max(t)$, with
  $ b^m P_t (b) = F(t). $
  For $L = 1$ these are the self-paying digits.
]

Under $0^0 = 0$ a block is the same as the solution $(t, 0, dots, 0)$ with $m$
zeros. Under $0^0 = 1$ that string instead has $P - F = -m$, because each
trailing zero costs 1. A block followed by any tail that pays for itself is a
solution (@cons-split). Under $0^0 = 1$ the only one-digit tail that pays for
itself is $(1)$, and a two-digit tail must be a 2-digit solution of the base.

#computation(id: "cons-blocks", title: "All blocks with small digits", src: "22.2")[
  With $L >= 2$, digits up to 40 to 150, and bases in the complete range of
  each search, there are exactly four self-paying blocks:
  $(1, 3)$ in base 4 and $(1, 7)$ in base 904, both at shift 1;
  $(6, 6, 5)$ in base 11 at shift 2; and $(3, 3, 6, 6)$ in base 13 at
  shift 1.
]

Each of them explains known solutions. $(1, 3)$ and $(1, 7)$ followed by the
digit 1 give $(1, 3, 1)$ in base 4 and $(1, 7, 1)$ in base 904. The block
$(3, 3, 6, 6)$ followed by 1 gives the 5-digit solution $(3, 3, 6, 6, 1)$ in
base 13:
$ 13 dot P_((3,3,6,6))(13) = 13 dot 7182 = 93366 = 3^3 + 3^3 + 6^6 + 6^6. $
The block $(6, 6, 5)$ gives $(6, 6, 5, 0, 0)$ and $(6, 6, 5, 0, 1)$ in base 11
under $0^0 = 0$, from $6 dot 11^4 + 6 dot 11^3 + 5 dot 11^2 = 96437 =
6^6 + 6^6 + 5^5$.

How often should blocks occur? A block is one equation in $L + 1$ unknowns,
while a solution of $L + m$ digits is one equation in $L + m + 1$ unknowns. The
coincidence model of @ch-model gives the rate.

#heuristic(id: "cons-block-rate", title: "Rate of blocks", src: "22.2")[
  The expected number of blocks of $L$ digits at shift $m$ in base $b$ is
  smaller than the expected number of solutions with $L + m$ digits by a factor
  of about $(k slash L) X^m$, where $k = L + m$ and $X = X_k (b)$ is the
  largest usable digit. Both rates fall like $b^(-(k-1))$ up to powers of
  $log b$, so the expected total over all bases is finite for every
  $L >= 2$.
]

The exact rates computed in #lib("22.2") follow this law within a factor
1.5, and a base-by-base calibration finds 2 blocks from base 13 on, against
0.73 expected. Blocks are coincidences, like solutions, only rarer. The
self-paying digits ($L = 1$) are the exception: $x b^m = x^x$ is an identity
that holds whenever $x^(x-1)$ is an $m$-th power.

Blocks were studied because of three 5-digit solutions in bases 13 to 99 that
seemed too many for the root heuristic (@sec-short-heuristic).
@tab-cons-five shows their structure.

#tablefig(
  caption: [The 5-digit solutions in bases 13 to 99 under $0^0 = 1$ and their
  remainders $R_m$ at each split (#lib("22.1")).],
  id: "tab-cons-five",
)[
  #btable(
    columns: 8,
    align: (right, left, right, left, right, right, right, right),
    [base], [digits], [$n$], [largest weights], [$R_1$], [$R_2$], [$R_3$], [$R_4$],
    [13], [$(3, 3, 6, 6, 1)$], [93,367], [$6^6 + 6^6$: 99.94%], [0], [46,578], [92,220], [85,656],
    [14], [$(2, 6, 0, 3, 6)$], [93,344], [$6^6 + 6^6$: 99.97%], [46,650], [46,635], [46,636], [76,828],
    [48], [$(3, 8, 6, 2, 0)$], [16,823,904], [$8^8$: 99.72%], [1], [$-91$], [32,741], [15,925,221],
  )
]

The first is an exact block followed by the digit 1. The third is a block
with remainder 1 followed by a 0, which weighs 1; by @cons-split this is the
same pattern with the last digit 0 instead of 1. The second has no structure
at all. None has a self-paying digit, since 13, 14 and 48 are not perfect
powers, and none belongs to a binomial family. Blocks are already counted by
the root heuristic: the polynomial of $(t, 1)$ is the polynomial of the block
$(t, b, 1)$. So blocks do not explain the excess, which remains a fluctuation
with probability about 0.005, or 0.015 after the choice of the cell
(@sec-short-heuristic).

== Many solutions in one base <sec-cons-many>

How large can $N_m (b)$ be? Under $0^0 = 0$ self-paying digits make it
unbounded. The cleanest family uses towers $n^(n-1)$.

#proposition(id: "thm-many-m0", title: [Unbounded counts under $0^0 = 0$], src: ("4.1", "9.8"))[
  For every $n >= 3$, base $n^(n-1)$ has at least $2^(n-1) - 2$ nontrivial
  solutions under $0^0 = 0$. So $N_0 (b)$ is unbounded.
]
#proof[
  For $1 <= s <= n - 2$, the digit $a = n^s$ is below $b = n^(n-1)$ and
  $a^(a-1) = n^(s(n^s - 1))$. Since $n - 1$ divides $n^s - 1$, this is $b^k$
  with $k = s(n^s - 1) slash (n - 1)$. So base $b$ has at least $n - 2$
  self-paying digits, and @cons-sp-count gives the count.
]

Here $ln b = (n - 1) ln n$, so $n$ grows like $ln b slash ln ln b$ and the
count is $b^((ln 2 + o(1)) slash ln ln b)$. That is faster than any power of
$log b$ and slower than any power of $b$. Powers of 2 give another family:
base $2^(L(2^L - 1))$ has the self-paying digits $2^(j L)$ for
$1 <= j <= 2^L - 2$ (#lib("4.1")).

#tablefig(
  caption: [The smallest base with at least $C$ self-paying digits, and the
  resulting lower bound for $N_0 (b)$ (#lib("9.8")). Most records are the
  towers $(C + 2)^(C + 1)$; the others are powers of 2, 3, 5 and 6 whose
  exponents have many divisors.],
  id: "tab-cons-records",
)[
  #btable(
    columns: 4,
    align: (right, left, right, right),
    [$C$], [smallest base], [size], [solutions, at least],
    [1], [$2^3$], [$10^(0.9)$], [2],
    [2], [$2^6$], [$10^(1.8)$], [6],
    [3], [$5^4$], [$10^(2.8)$], [14],
    [5], [$7^6$], [$10^(5.1)$], [62],
    [8], [$10^9$], [$10^(9.0)$], [510],
    [14], [$2^(60)$], [$10^(18.1)$], [32,766],
    [23], [$5^(48)$], [$10^(33.6)$], [16,777,214],
    [30], [$2^(155)$], [$10^(46.7)$], [2,147,483,646],
    [39], [$41^(40)$], [$10^(64.5)$], [1,099,511,627,774],
  )
]

These bases are rare.

#proposition(id: "cons-rare", title: "Rich bases are rare", src: "9.8")[
  At most $X^(1 slash (c + 1))$ bases up to $X$ have $c$ or more self-paying
  digits.
]
#proof[
  By @thm-self-paying the self-paying digits of $b = r^t$ are $r^s$ with
  $s < t$. So $c$ of them need $t >= c + 1$, and $b$ is a perfect
  $(c + 1)$-th power.
]

So the structure that produces many solutions lives on a set of density zero.
The average count, about 1.5 per base under $0^0 = 0$ in the model, comes from
coincidences with a Poisson law and no heavy tail (@ch-model). The extremes
come from a different source than the average.

Under $0^0 = 1$ the picture is different, and the question whether $N_1 (b)$
is bounded is open. Every placement of balance zero is now a self-paying
digit or a final 1, since a zero costs 1. A solution made only of such
placements needs a self-paying digit at every position above 0, and by
@cons-sp-spacing no two of them are adjacent. So the only such solutions are
$(a, 1)$ in base $a^(a-1)$ (#lib("8.3")). Self-paying digits help only
together with near-solutions.

#proposition(id: "cons-near", title: [Self-paying digits under $0^0 = 1$], src: "8.4")[
  Under $0^0 = 1$, consider strings of a fixed length $L$, leading zeros
  allowed, in which every zero weighs 1. The solutions of length $L$ with $j$
  self-paying digits correspond exactly to the pairs made of a string $n$ with
  $F(n) = n + j$ (a near-solution with defect $j$) and a choice of $j$
  self-paying positions where $n$ has a 0, such that the result does not start
  with 0.
]
#proof[
  Each self-paying digit placed on a 0 raises $n$ and $F(n)$ by the same
  amount, minus the weight 1 of the zero it replaces in $F$. So it lowers the
  defect $F(n) - n$ by exactly 1.
]

Base 64 shows the mechanism. Removing the self-paying 16 and 4 from
$(16, 0, 0, 0, 0, 0, 1, 0, 0, 4, 8)$ leaves $(0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 8)$,
whose weight $9 + 1 + 8^8 = 16777226$ exceeds its value $64^4 + 8 = 16777224$
by 2. A construction like @thm-many-m0 would need near-solutions of every
small defect in one base, and none is known. The chain construction of
@cons-chains could in principle give $binom(n, k)$ solutions in one base, if a
chain reached a position above $n$ self-paying digits, but the search of
@cons-chain-census found no instance.

== Integers with several bases <sec-cons-multibase>

By @thm-one-base a digit string is a solution in at most one base. An integer
is another matter: it has a different digit string in each base, and it can be
a solution in several.

#proposition(id: "cons-many-bases", title: [Many bases under $0^0 = 0$], src: "15.6")[
  Under $0^0 = 0$, let $c = r^u$ with $r$ not a perfect power. Then
  $N = c^c + 1$ is a solution in every base $r^t$ with $u < t$ and
  $t divides u(c - 1)$, and in base $c^c - c + 1$. So one integer can be a
  solution in arbitrarily many bases.
]
#proof[
  In base $r^t$ the digit $c$ is self-paying at position $k = u(c - 1) slash t$,
  so $(c, 0, dots, 0, 1)$ with $k + 1$ digits is a solution, with value
  $c^c + 1$. In base $c^c - c + 1$ the string $(1, c)$ is a solution with the
  same value. The number of divisors of $u(r^u - 1)$ is unbounded.
]

#example(id: "cons-multibase-examples")[
  - For $c = 256 = 2^8$, $8 dot 255 = 2040$ has 25 divisors above 8. So
    $2^(2048) + 1$ is a solution in 26 bases. A complete search confirms that
    these are all.
  - $7^7 + 1 = 823544$ is a solution in five bases under $0^0 = 0$: 49, 343
    and $7^6 = 117649$ (the self-paying 7), 823537 (the string $(1, 7)$), and
    904 (the string $(1, 7, 0)$).
  - $28 = 3^3 + 1$ is a solution in bases 9 and 25, as $(3, 1)$ and $(1, 3)$,
    and also as $(1, 3, 0)$ in base 4 and $(1, 0, 3)$ in base 5.
]

Under $0^0 = 1$ the two-digit representations are rigid.

#proposition(id: "cons-two-reps", title: [Two-digit representations under $0^0 = 1$], src: "15.6")[
  Under $0^0 = 1$, an integer $N >= 3$ has at most two 2-digit representations
  as a solution. If it has two, they are $(a, c)$ and $(c, a)$ with
  $N = a^a + c^c$, $a divides c^c - c$ and $c divides a^a - a$.
]
#proof[
  A 2-digit solution has $N = w(a) + w(c)$. If $X^X + Y^Y = U^U + V^V$ with
  $X >= Y$, $U >= V$ and $X > U$, then $X^X >= (U + 1)^(U+1) > 2 U^U$, which is
  impossible. So the pair of weights is unique, and its two orders give at
  most two strings.
]

So $N = c^c + 1$ has the two bases of $(1, c)$ and $(c, 1)$ for every
$c >= 2$, and a third base needs a representation with three or more digits.
To find every base of a given integer, one needs a bound on where its base can
lie. The leading digit and the second digit pin it down.

#lemma(id: "cons-window", title: "Window for the base", src: ("15.6", "20.1"))[
  Let $n$ be a solution in base $b$ with $k >= 2$ digits, leading digit $p$
  and largest digit $M$. Then
  $ p b^(k-1) <= n < p b^(k-1) + (M + 1) b^(k-2) $
  and so
  $ b <= (n slash p)^(1 slash (k - 1)) < b + (M + 1) / (p (k - 1)). $
]
#proof[
  The digits after the second one add at most $b^(k-2) - 1$, and the second
  digit is at most $M$. For the second claim put $u = (M + 1) slash (p b)$, so
  that $n slash p < b^(k-1) (1 + u)$, and use Bernoulli's inequality
  $(1 + u)^(1 slash (k-1)) <= 1 + u slash (k - 1)$.
]

All 3,135 known solutions satisfy both inequalities, and the window is close
to sharp. Under $0^0 = 1$ an integer with a 2-digit representation has very
constrained longer representations.

#lemma(id: "cons-rigid", title: "Rigid representations", src: "18.3")[
  Under $0^0 = 1$, let $N = a^a + w(c)$ with $0 <= c <= a$ and $a >= 2$. Every
  representation of $N$ as a solution in some base contains the digit $a$
  exactly once, unless it is $(a, a)$, and its other digits are below $c$ with
  weights adding up to $w(c)$. So if $c <= 1$ or $c = a$, every representation
  of $N$ has 2 digits, and if $2 <= c < a$, every longer one has between
  $c + 2$ and $a + 1$ digits.
]

#corollary(id: "cons-three-bases", title: "Three bases", src: "18.3")[
  An integer with three bases under $0^0 = 1$ either has at most one 2-digit
  representation and at least two longer ones, or it is $N = a^a + c^c$ with
  $2 <= c < a$, $c divides a^a - a$, $a divides c^c - c$, and a third
  representation of $c + 2$ to $a + 1$ digits: one digit $a$ and digits below
  $c$ whose weights add up to $c^c$.
]

#computation(id: "cons-multibase-census", title: "Integers with several bases", src: ("15.6", "18.3"))[
  Under $0^0 = 1$: of the 2,117 integers with a 2-digit representation with
  digits up to 90, 1,779 have one base, 338 have two, and none has three or a
  representation with 3 or more digits. None of the 483 integers $a^a + c^c$
  with two 2-digit bases and $a, c <= 150$ has a third base. Under $0^0 = 0$:
  among all known solutions and all $a^a + w(c)$ with $a, c <= 40$, 428
  integers have two or more bases; in all but two of those with a longer
  representation, every such representation comes from self-paying digits or
  swaps. The exceptions are 28 and 823544. The maximum is 26 bases, for
  $2^(2048) + 1$.
]

So under $0^0 = 0$ the number of bases of an integer is unbounded, through
self-paying digits, while under $0^0 = 1$ no integer with three bases is known.
A third base would need a coincidence of the kind that @ch-short studies, and
no reason is known why one cannot exist.
