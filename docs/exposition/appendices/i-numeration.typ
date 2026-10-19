#import "../template.typ": *

= Numeration systems <app-numeration>

@ch-worlds asks the Munchausen question in number systems other than the positive integer bases: negative bases, complex bases, rational bases, a Pisot base, the factorial system, and polynomial bases over a finite field (@app-ffield). Each system needs three things: a digit set, a proof that every number has exactly one expansion, and a description of which residues the digit multiset fixes. This appendix supplies them. Knuth @knuth1997[section 4.1] covers negative and complex bases with many historical notes.

== The common pattern: the identity modulus <sec-app-numeration-identity>

In base $b$ every integer satisfies $n equiv$ (digit sum) $med (mod b - 1)$, because $b equiv 1 med (mod b - 1)$. The same argument works for any base $beta$ in a ring: modulo $beta - 1$ every power of $beta$ is 1, so
$ n = sum_i s_i beta^i equiv sum_i s_i med (mod beta - 1) . $
When $beta$ is an algebraic integer and $beta - 1$ is primitive (not divisible by a rational integer greater than 1), a rational integer is divisible by $beta - 1$ exactly when it is divisible by the norm $N(beta - 1)$. So the identity becomes a congruence modulo the integer $M = abs(N(beta - 1))$, the identity modulus. For a Munchausen number $n = F(n)$ it reads $sum (w(x) - x) equiv 0 med (mod M)$, as in @thm-digit-sum.

No other modulus is a function of the digit multiset. Swapping two adjacent digits $x$ and $y = x - 1$ at the bottom changes the value by $(x - y)(beta - 1) = beta - 1$ and keeps the multiset. So any modulus that the multiset determines divides $beta - 1$ (@thm-only-residue). @sec-worlds-frame shows that this one modulus governs the parity effect in every system: the expected count doubles when $M$ is even and $w(x) equiv x med (mod 2)$.

#align(center, btable(
  columns: 4,
  align: (left, left, left, left),
  [system], [digits], [identity modulus $M$], [parity doubling under $0^0 = 0$],
  [base $b$], [$0, dots, b - 1$], [$b - 1$], [$b$ odd],
  [base $-b$], [$0, dots, b - 1$], [$b + 1$], [$b$ odd],
  [base $-n + i$], [$0, dots, n^2$], [$(n + 1)^2 + 1$], [$n$ even],
  [base $-n + omega$], [$0, dots, n^2 + n$], [$n^2 + 3n + 3$], [never],
  [base $p slash q$], [$0, dots, p - 1$], [$p - q$], [$p, q$ odd],
  [base $epsilon_x$], [$0, dots, x$], [$x$], [$x$ even],
  [factorial], [$0, dots, i$ at position $i$], [none], [never],
))

== Negative bases <sec-app-numeration-negative>

#theorem(id: "app-numeration-negabase", title: "Negative bases", status: "cited")[
  Let $b >= 2$. Every integer $n$, positive, negative or zero, has exactly one expansion $n = sum_i s_i (-b)^i$ with digits $0 <= s_i <= b - 1$.
]

The proof is division with remainder: $s_0$ is the residue of $n$ modulo $b$ in ${0, dots, b - 1}$, and the rest is the expansion of $(n - s_0) slash (-b)$. Negative bases go back to Grunwald in 1885 (see @knuth1997). Since $-b equiv 1 med (mod b + 1)$, the identity modulus is $b + 1$. Two facts are used by the search engine of @sec-worlds-negative (#lib("14.1")):

- The integers with at most $j$ digits form an interval $[-m_j, M_j]$, where $M_j$ sums $(b - 1) b^i$ over the even positions $i < j$ and $m_j$ over the odd ones. Fixing the top digits gives a translate of this interval. So the prefix tree of @sec-search-tree works.
- A positive integer has an odd number of digits, because the leading term outweighs the rest and has the sign of $(-b)^(k-1)$. So Munchausen numbers in negative bases have odd length.

Example: in base $-10$, $404201091 = (4, 0, 5, 8, 1, 9, 1, 1, 1)$, and it equals $4^4 + 1 + 5^5 + 8^8 + 1 + 9^9 + 1 + 1 + 1$ under $0^0 = 1$ (#lib("12.3")).

== Complex bases and canonical number systems <sec-app-numeration-cns>

#definition(id: "app-numeration-def-cns", title: "Canonical number system")[
  Let $beta$ be an algebraic integer with minimal polynomial $P$ and let $N = abs(P(0))$. The pair $(beta, {0, 1, dots, N - 1})$ is a canonical number system if every element of $ZZ[beta]$ has a finite expansion $sum_i s_i beta^i$ with digits in ${0, dots, N - 1}$.
]

Expansions in a canonical number system are automatically unique, since the digits form a complete set of residues modulo $beta$. Katai and Szabo @katai-szabo1975 showed that the Gaussian integers $-n + i$, $n >= 1$, are canonical number system bases, with digits $0, dots, n^2$. For quadratic bases there is a complete criterion.

#theorem(id: "app-numeration-quadratic-cns", title: "Quadratic canonical number systems", status: "cited")[
  A root $beta$ of an irreducible polynomial $t^2 + B t + C$ with integer coefficients is a canonical number system base exactly when $-1 <= B <= C$ and $C >= 2$.
]

See Katai and Kovacs @katai-kovacs1980 and Gilbert @gilbert1981. The Eisenstein bases $beta = -n + omega$, with $omega^2 + omega + 1 = 0$, are roots of $t^2 + (2n + 1) t + (n^2 + n + 1)$, which satisfies the criterion. Their identity modulus is $N(beta - 1) = n^2 + 3n + 3$, an odd number for every $n$. That is why the parity effect is absent there (@sec-worlds-complex).

Imaginary bases $c i$ with $c >= 2$ and digits $0, dots, c^2 - 1$ reduce to negative bases: $(c i)^2 = -c^2$, so the digits at even positions form an expansion in base $-c^2$, and a rational integer has zeros at all odd positions. Knuth's quater-imaginary base $2i$ is the case $c = 2$.

In complex bases the expansions of positive integers do not use every length. In base $-1 + i$ one has $(-1 + i)^4 = -4$, so an integer is its base $-4$ expansion written in blocks of four binary digits, and its length is $equiv 1$ or $4 med (mod 8)$ (#lib("23.4")).

== Rational bases <sec-app-numeration-afs>

Akiyama, Frougny and Sakarovitch @akiyama-frougny-sakarovitch2008 defined a number system with base $p slash q$, for coprime $p > q >= 1$.

#theorem(id: "app-numeration-afs", title: "Rational base expansions", status: "cited")[
  Every positive integer $N$ has exactly one expansion
  $ N = sum_i a_i / q (p / q)^i, quad 0 <= a_i <= p - 1 . $
  The digits come from the recursion $N_0 = N$ and $q N_i = p N_(i+1) + a_i$, where $a_i$ is the residue of $q N_i$ modulo $p$.
]

The integers form a tree: the expansion of $N$ is that of its parent $(q N - a_0) slash p$ followed by $a_0$. The set of all expansions is not a regular language, which makes the system subtle, but the tree makes it easy to search (#lib("21.2")). Reducing the recursion modulo $p - q$, where $p equiv q$, gives $q N equiv$ (digit sum) $med (mod p - q)$, so the identity modulus is $p - q$, unrelated to the digit range $p$. Example: $8 = (2, 1, 0, 1, 1)$ in base $3 slash 2$, since $(2 slash 2)(3 slash 2)^4 + (1 slash 2)(3 slash 2)^3 + (1 slash 2)(3 slash 2) + 1 slash 2 = 8$, and $2^2 + 1 + 1 + 1 + 1 = 8$ under $0^0 = 1$.

== Beta-expansions and Pisot bases <sec-app-numeration-beta>

For a real $beta > 1$, the greedy expansion of a positive real number takes the largest power $beta^k$ below it, the largest digit $d$ with $d beta^k$ below it, and continues with the remainder. The digits lie in ${0, dots, ceil(beta) - 1}$. Parry @parry1960 characterized the digit strings that arise: a string is admissible when each of its tails is lexicographically smaller than the expansion of 1.

#definition(id: "app-numeration-def-pisot", title: "Pisot number")[
  A Pisot number is a real algebraic integer $beta > 1$ whose other conjugates all have absolute value less than 1.
]

The golden ratio and $epsilon_x = (x + sqrt(x^2 + 4)) slash 2$, the root of $t^2 - x t - 1$, are Pisot numbers. Pisot bases behave like integer bases in one key way.

#theorem(id: "app-numeration-finite", title: "Frougny and Solomyak", status: "cited")[
  If $beta$ is a root of $t^d - a_1 t^(d-1) - dots - a_d$ with integers $a_1 >= a_2 >= dots >= a_d >= 1$, then every positive element of $ZZ[1 slash beta]$, in particular every positive integer, has a finite greedy expansion.
]

See @frougny-solomyak1992. For $epsilon_x$ the coefficients are $x >= 1$, so every positive integer has a finite expansion, with digits $0, dots, x$ and every digit $x$ followed by a 0. Expansions of integers can have digits after the radix point: for the golden ratio, $2 = phi + phi^(-2)$. The norm of $epsilon_x - 1$ is $-x$, so the identity modulus is $x$ (#lib("21.4")).

== The factorial number system <sec-app-numeration-factorial>

Every positive integer has exactly one expansion $n = sum_(i=1)^L d_i i!$ with $0 <= d_i <= i$ and $d_L >= 1$. This is a mixed-radix system: the digit at position $i$ is the remainder after dividing by $i + 1$. Here no modulus is a function of the digit multiset: $(1, 0, 1)$ and $(1, 1, 0)$ have the same multiset and the values 7 and 8. A digit $v$ can only sit at a position $i >= v$, so the large digits are confined to the top positions. @sec-worlds-factorial shows that this is exactly what makes the probabilistic model fail there (#lib("21.5")).
