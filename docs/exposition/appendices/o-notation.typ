#import "../template.typ": *

= Notation and glossary <app-notation>

== Notation <sec-app-notation-symbols>

#btable(
  columns: (auto, 1fr, auto),
  align: (left, left, left),
  [symbol], [meaning], [see],
  [$b$], [the base, an integer $b >= 2$ unless a chapter says otherwise], [@sec-basics-def],
  [$m$], [the convention: the value of $0^0$, which is 0 or 1], [@sec-basics-conventions],
  [$w(x)$], [the weight of a digit: $x^x$ for $x >= 1$, and $w(0) = m$], [@sec-basics-def],
  [$F(n)$, $F(s)$], [the Munchausen sum: the sum of the weights of the digits], [@sec-basics-def],
  [$F_0$, $F_1$], [the sum under $0^0 = 0$ and under $0^0 = 1$], [@sec-basics-conventions],
  [$(s_(k-1), dots, s_0)$], [a digit string, most significant digit first; position 0 is the last digit], [@sec-basics-def],
  [$k$], [the number of digits of a string or a solution], [],
  [$J$], [$b - k$, how far the length of a solution is below the base], [@sec-model-window],
  [$c_x$], [the number of copies of the digit $x$; the vector $c$ is the digit multiset], [@sec-basics-def],
  [$z(n)$], [the number of zero digits of $n$], [@sec-basics-conventions],
  [$N_m (b)$], [the number of nontrivial solutions in base $b$ under convention $m$], [@sec-model-data],
  [$N_(m,k)(b)$], [the number of those with $k$ digits], [],
  [$X_k (b)$], [the largest digit $x$ with $x^x < b^k$], [@sec-basics-length],
  [$P_s (r)$], [the value polynomial $sum_i s_i r^i$ of a digit string], [@sec-basics-polynomial],
  [$Q_s (r)$], [the Munchausen polynomial $P_s (r) - F(s)$; $s$ is a solution in base $b$ exactly when $Q_s (b) = 0$ and $b$ exceeds every digit], [@sec-basics-polynomial],
  [$g(c)$], [$w(c) - c$], [@sec-cons-two-digit],
  [$T(q)$], [the set of residues of $x^x - x$ modulo $q$], [@sec-short-coverings],
  [$h(alpha)$], [the absolute logarithmic height of an algebraic number], [@sec-app-baker-height],
  [$eta$], [the fundamental unit $> 1$ of a real quadratic field], [@sec-short-regimes],
  [$rho_s (p)$], [the number of roots of $Q_s$ modulo $p$], [@sec-short-heuristic],
  [$D$], [an offset: near-solutions satisfy $n - F(n) = D$], [@sec-model-defects],
  [$lambda_m (b)$], [the mean number of near-solutions per offset, an estimate of the expected $N_m (b)$], [@sec-model-defects],
  [$s_j$], [the limit share of the length $b - j$ in the basic model], [@sec-model-shares],
  [$d_"TV"$], [total variation distance between two laws], [@sec-app-prob-poisson],
  [$e(t)$], [$e^(2 pi i t)$, an additive character], [@sec-model-assumption-r],
  [$rho(b)$], [the largest normalized exponential sum of $x^x - x$ modulo $b - 1$; Assumption R holds when it is below $1 - 3 ln b slash b$], [@sec-model-assumption-r],
  [$rho^*(b)$], [the largest share of one residue class modulo $b - 1$ among the strings of the refined coupled model], [@sec-model-anticonc],
  [$tau(n)$], [the number of divisors of $n$], [@sec-app-quadratic-two-squares],
  [$L(b)$], [the number of digits of $(b-1)!$, for factorions], [@sec-worlds-weights],
  [$k(B)$], [the free residue dimension of a base $B$ in $FF_q [T]$; equal to $omega(B - 1)$ in most cases], [@sec-worlds-ffield],
  [$omega(B - 1)$], [the number of distinct monic irreducible factors of $B - 1$], [@sec-worlds-ffield],
  [$ln$, $log$], [natural logarithm; $log_2$ and $log_b$ carry their base], [],
  [$a | b$], [$a$ divides $b$], [],
  [$a equiv b med (mod q)$], [$q$ divides $a - b$], [],
  [$||y||$], [the distance from the real number $y$ to the nearest integer], [@sec-short-square],
)

== Glossary <sec-app-notation-glossary>

#let term(name, body, where) = block(above: 0.7em, below: 0.7em)[
  #strong(name). #body #if where != none [(#where)]
]

#term[Solution][A Munchausen number with at least two digits, so not 0 or 1. Short for "nontrivial solution".][@sec-basics-def]

#term[Shared solution][A solution without the digit 0. It is a solution under both conventions.][@thm-conventions]

#term[Twins][Under $0^0 = 0$, a solution that ends in 0 and the number one larger, which is also a solution.][@thm-twins]

#term[Balance][The amount $x b^i - w(x)$ that a digit $x$ at position $i$ adds to $n - F(n)$. A number is a solution when its balances add up to 0.][@sec-basics-balance]

#term[Self-paying digit][A digit $a >= 2$ at a position $k >= 1$ with $a b^k = a^a$. It adds the same amount to $n$ and to $F(n)$. Only perfect-power bases have them.][@sec-cons-selfpaying]

#term[Core][What remains of a solution under $0^0 = 0$ after removing its self-paying digits and a final 1.][@thm-structure-m0]

#term[Swap][Two digits that pay for each other: $a$ at position $k$ and $a^a$ at position 0, with $a b^k = (a^a)^(a^a)$.][@sec-cons-swaps]

#term[Self-paying block][A string $t$ with $b^m P_t (b) = F(t)$ for some shift $m >= 1$. A tail that pays for itself completes it to a solution.][@sec-cons-blocks]

#term[Binomial family][The solutions of @thm-binomial, whose leading digits are the binomial coefficients of $(c r + e)^(k-1)$. They give infinitely many solutions of every length under both conventions.][@sec-cons-binomial]

#term[Free slot][A position of a search node that will hold a digit below the current value, still unknown. Nodes with one free slot are 43% of the exact tree in base 28, and the residue rule acts on them.][@sec-search-residue]

#term[Height][A measure of how complicated an algebraic number is, roughly the number of digits needed to write it down. Lower bounds for linear forms in logarithms depend on it.][@sec-app-baker-height]

#term[Digit-sum identity][$n equiv$ (digit sum of $n$) $mod (b - 1)$, which for a solution becomes a condition on the digit multiset.][@thm-digit-sum]

#term[Identity modulus][The modulus of the digit-sum identity in a number system: $b - 1$ for base $b$, $b + 1$ for base $-b$, $N(beta - 1)$ for a complex base $beta$, $p - q$ for the rational base $p slash q$.][@sec-worlds-frame]

#term[Parity effect][In odd bases under $0^0 = 0$ the digit-sum identity holds modulo 2 for free, which doubles the expected number of solutions.][@sec-model-refined]

#term[Basic model, refined model][The probabilistic model that treats the digits of $F(c)$ as random, without and with the digit-sum identity.][@sec-model-basic]

#term[Near-solution, offset, defect spectrum][A number with $n - F(n) = D$ for a small offset $D$. The counts over many offsets measure each base's own rate of coincidences.][@sec-model-defects]

#term[Forced top digits][The leading digits of $F(c)$, which the counts of the largest digits fix. They are the main known correction to the model.][@sec-model-defects]

#term[Root heuristic][The heuristic for short solutions: the chance that the real root of $Q_s$ is an integer, times local factors.][@sec-short-heuristic]

#term[Local obstruction][A modulus $q$ for which $Q_s$ has no root modulo $q$. Then $s$ is a solution in no base.][@thm-local]

#term[Covering][A finite set of moduli that excludes every value of one varying digit of a string family.][@sec-short-coverings]

#term[Square class][The case where the dominant term of the equation of a short string is a perfect power, so that the equation is close to a difference of powers.][@sec-short-square]

#term[Pure and mixed solutions][For $b(b + x) = x^n + 1$ with odd $x$: whether the ideal $B$ with $(b + epsilon) = B^n$ takes all its primes from one of the two conjugate ideals above $x$ or mixes them.][@sec-dio-field]

#term[Aurifeuillian factors][The two algebraic factors $L < M$ into which $x^x + 1$ or $x^x - 1$ splits for squarefree odd $x$ of the right residue modulo 4.][@sec-dio-aurifeuille]

#term[Prefix-pruned tree][The exact search: it fixes the digit counts from the largest digit down and prunes with the leading digits that the interval of possible sums shares.][@sec-search-tree]

#term[Inexact search][A search that skips nodes the model calls unlikely, with a measured miss rate.][@sec-search-inexact]

#term[Tally language][A set of words over a one-letter alphabet, such as the bases written in unary that have a solution.][@sec-search-complexity]

#term[Factorion][A number equal to the sum of the factorials of its digits.][@sec-worlds-weights]

#term[Narcissistic number][A $k$-digit number equal to the sum of the $k$-th powers of its digits.][@sec-worlds-weights]

#term[Frobenius block][In $FF_q [T]$, the $q$ digits that one base-$B$ digit becomes under $n |-> n^q$.][@sec-worlds-ffield]
