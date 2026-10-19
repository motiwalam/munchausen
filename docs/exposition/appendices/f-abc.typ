#import "../template.typ": *

= The abc conjecture <app-abc>

Several finiteness statements in @ch-short, @ch-diophantine and @ch-worlds are proven only on the assumption of the abc conjecture. This appendix states the conjecture, explains how it is measured, and shows how it applies to the equations of the main text. Granville and Tucker @granville-tucker2002 give a readable survey.

== The radical and the conjecture <sec-app-abc-statement>

#definition(id: "app-abc-def-radical", title: "Radical and quality")[
  The radical $"rad"(n)$ of a positive integer $n$ is the product of the distinct primes that divide $n$. For coprime positive integers $a + b = c$, the quality of the triple is
  $ q(a, b, c) = (ln c) / (ln "rad"(a b c)) . $
]

For most triples $"rad"(a b c)$ is much larger than $c$, and the quality is below 1. A high quality needs $a$, $b$ and $c$ to be divisible by high powers of small primes. For example $1 + 8 = 9$ has radical 6 and quality $ln 9 slash ln 6 approx 1.226$.

#conjecture(id: "app-abc-conj", title: "The abc conjecture of Masser and Oesterle")[
  For every $delta > 0$ there is a constant $K_delta$ such that every coprime triple $a + b = c$ of positive integers satisfies $c < K_delta "rad"(a b c)^(1 + delta)$. Equivalently, for every $delta > 0$ only finitely many triples have quality above $1 + delta$.
]

Infinitely many triples have quality above 1, so the exponent $1 + delta$ cannot be replaced by 1. The best known triple is due to Reyssat:
$ 2 + 3^(10) dot 109 = 23^5, quad q = (ln 23^5) / (ln(2 dot 3 dot 109 dot 23)) approx 1.6299 . $

The conjecture is widely believed and widely used as a heuristic guide. A proof has been claimed (Mochizuki, 2012), but that proof is not accepted by most experts, and this document treats the conjecture as open. Much weaker forms are also unproven: no one knows how to show that $c < K "rad"(a b c)^(2 - delta)$ for some fixed $delta > 0$. The best unconditional bounds, from linear forms in logarithms (@app-baker), are exponential in a power of the radical.

== An explicit form <sec-app-abc-explicit>

The constant $K_delta$ in the conjecture is not known, so the conjecture alone gives finiteness but no explicit bound. A. Baker proposed an explicit version. Laishram and Shorey @laishram-shorey2012 showed that Baker's explicit conjecture implies a simple statement.

#conjecture(id: "app-abc-explicit", title: "An explicit abc inequality")[
  Every coprime triple $a + b = c$ of positive integers satisfies $c < "rad"(a b c)^(7 slash 4)$.
]

This is much weaker than the full conjecture for large triples, but it has no unknown constant. It turns a finiteness statement into a bound that a computer can reach. The exposition uses it in @short-abc-explicit and @worlds-fact-abc. No triple with quality above 1.63 is known, so the exponent $7 slash 4$ leaves a wide margin.

The conjecture is about three terms. Browkin and Brzezinski @browkin-brzezinski1994 proposed a version for $n$ terms, with exponent $2n - 5 + delta$. For four terms this is 3, too weak for the equations of the library with two large digits.

== Consequences <sec-app-abc-consequences>

The conjecture implies many finiteness theorems at once. Two examples near the main text:

- Brocard's equation $n! + 1 = m^2$ has only finitely many solutions (Overholt @overholt1993). The known ones are $n = 4, 5, 7$.
- Fermat's equation $x^p + y^p = z^p$ has no solution with $x y z != 0$ for all large $p$, because a solution would be a triple of quality at least $p slash 3$.

The pattern in both: an equation produces a triple $a + b = c$ in which two terms are high powers or have only small prime factors, so the radical is much smaller than $c$.

== Use in the main text <sec-app-abc-use>

#example(title: [The equation $b(b + x) = x^n + 1$])[
  Completing the square gives $(x^2 + 4) + 4 x^n = (2b + x)^2$ for odd $x$. This is a coprime triple, and its radical is at most $2 x (x^2 + 4)(2b + x)$, which is about $4 x^(3 + n slash 2)$, while $c$ is about $4 x^n$. The quality is therefore about $n slash (3 + n slash 2)$, which tends to 2. So the full abc conjecture implies that the equation has only finitely many solutions with $n >= 7$, and even the weak form with exponent $2 - delta$ is enough (@sec-dio-exponents). For the diagonal $n = x$ the library sieves every $x <= 4 dot 10^9$, so any further solution of $b(b + x) = x^x + 1$ would be a triple of quality above $2 - 10^(-8)$ (#lib("16.2")). The record is 1.6299.
]

#example(title: "Cores in perfect-power bases")[
  Under $0^0 = 0$, a 2-digit solution $(a, c)$ in a base $b = r^t$ with $t >= 2$ gives $a r^t = a^a + c^c - c$. When one of $a^a$ and $c^c$ is much larger than the other, this is an abc triple with two large terms that are powers, and the conjecture leaves only finitely many such solutions (@sec-dio-cores, Theorem 15.10 of #lib("15.3")). The case $a^a approx c^c$ has four large terms and is out of reach of abc.
]

#example(title: "Three-digit strings and factorions")[
  A 3-digit string with one large digit $x$ becomes $U^2 = N + R$ after completing the square, with $N = 4 ell x^x$ and $R$ small (@short-three-digit-class). The radical of $N$ is at most $2 ell x$, tiny compared with $N$, and $U$ is about $sqrt(N)$. So the triple has quality close to 2, and abc bounds $x$ by about twice the other digits (@short-abc-three). For factorions, $N = 4 ell dot x!$, and the radical of $x!$ is the product of all primes up to $x$, about $e^x$. The quality is now only about $ln(x!) slash (x + ln(x!) slash 2)$, which still tends to 2 but slowly. With the explicit exponent $7 slash 4$ the bound is $x <= 4","103","641$, almost independent of the other digits (@worlds-fact-abc).
]

So abc would settle several of the open problems of @ch-open in one stroke, but none of them needs the full strength of abc. The weak form with exponent $2 - delta$, which is also open, would already finish the family $(1, x, 1)$.
