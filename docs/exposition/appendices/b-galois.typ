#import "../template.typ": *

= Galois groups, Chebotarev and Jordan <app-galois>

A digit string $s = (s_1, dots, s_k)$ is a solution in base $b$ exactly when $b$ is a root of the Munchausen polynomial
$ Q_s (r) = s_1 r^(k-1) + s_2 r^(k-2) + dots + s_k - F(s) $
(@sec-basics-polynomial). @ch-short studies how this polynomial behaves modulo primes. The tools are the Galois group of a polynomial, the way it controls roots modulo primes, and a little group theory. This appendix states them. Good references are the survey of Stevenhagen and Lenstra @stevenhagen-lenstra1996, Serre's article on Jordan's theorem @serre2003, and Serre's book @serre-topics2008 for Hilbert irreducibility.

== The Galois group of a polynomial <sec-app-galois-group>

Let $f$ be a polynomial with rational coefficients, of degree $n$, without repeated roots. Its splitting field $K$ is the smallest field that contains $QQ$ and all $n$ complex roots of $f$.

#definition(id: "app-galois-def-group", title: "Galois group")[
  The Galois group $G$ of $f$ is the group of field automorphisms of $K$. Each automorphism permutes the roots of $f$, and it is determined by this permutation. So $G$ is a subgroup of the symmetric group $S_n$ on the roots, well defined up to a renumbering of the roots.
]

$G$ acts transitively on the roots exactly when $f$ is irreducible over $QQ$. For a "random" polynomial of degree $n$, the group is all of $S_n$. Hilbert's irreducibility theorem makes this precise: if a polynomial $f(t, r)$ in two variables has group $G$ over the field $QQ(t)$, then for all integers $t$ outside a thin set, which has density 0, the specialized polynomial has group $G$ again (@serre-topics2008[chapter 3]). For $Q_s$ the free parameter is the constant term $F(s)$, which has nothing to do with the other coefficients. So one expects the group $S_(k-1)$ for almost all strings. @sec-short-galois confirms this by the statistics below, and proves it for $k = 4$ and $k = 5$ once the digits are not too small (#lib("16.4")).

Smaller groups come from structure. A polynomial is decomposable if $P = G(h(r))$ with $G$ and $h$ of degree at least 2. Then the roots fall into blocks, one for each root of $G$, and the Galois group preserves the blocks. For example $Q_s$ for the string $(9, 18, 18, 9, 15)$ is a polynomial in $u = r^2 + r$, so its group lies in the dihedral group $D_4$ of order 8 (#lib("12.1")). Ritt's theory @ritt1922 describes all ways to decompose a polynomial. Two families of indecomposable polynomials have small groups for another reason: the power maps $r^n$ and the Dickson polynomials
$ D_n (r, a) = sum_(i=0)^(floor(n slash 2)) n/(n - i) binom(n - i, i) (-a)^i r^(n - 2i), $
which satisfy $D_n (y + a slash y, a) = y^n + (a slash y)^n$. For example $D_5 (r, -1) = r^5 + 5 r^3 + 5 r$. The strings $(1, 0, 5, 0, 5, x)$ have exactly this digit polynomial, and their group is the group $F_20$ of order 20 instead of $S_5$ (#lib("16.4")).

== Reduction modulo a prime <sec-app-galois-frobenius>

The roots of $f$ modulo a prime $p$ are visible in the Galois group. Let $f$ have integer coefficients, and let $p$ be a prime that does not divide the leading coefficient or the discriminant of $f$. Then $f mod p$ has no repeated factor, and it factors over $FF_p$ into irreducible factors of degrees $n_1, dots, n_r$ with $n_1 + dots + n_r = n$.

#theorem(id: "app-galois-dedekind", title: "Dedekind, Frobenius", status: "cited")[
  For such a prime $p$ there is an element $sigma_p$ of $G$, the Frobenius element, well defined up to conjugation, whose cycle type on the roots is $(n_1, dots, n_r)$. In particular $f$ has a root modulo $p$ exactly when $sigma_p$ fixes at least one root.
]

So the question "how often does $f$ have no root modulo $p$" becomes the question "how often is the Frobenius element a fixed-point-free permutation". The answer is the Chebotarev density theorem.

#theorem(id: "app-galois-chebotarev", title: "Chebotarev density theorem", status: "cited")[
  For every conjugacy class $C$ of $G$, the set of primes $p$ with $sigma_p$ in $C$ has natural density $|C| slash |G|$ among all primes.
]

#corollary(id: "app-galois-noroot", title: "Primes without a root", status: "cited")[
  The primes modulo which $f$ has no root have density equal to the share of elements of $G$ that fix no root. For $G = S_n$ this share is the share of derangements,
  $ D_n / n! = sum_(j=0)^n (-1)^j / j! , $
  which is $1 slash 2, 1 slash 3, 3 slash 8, 11 slash 30$ for $n = 2, 3, 4, 5$ and tends to $1 slash e approx 0.368$.
]

The formula for $D_n slash n!$ is inclusion and exclusion over the set of fixed points. The same formula gives the share of all polynomials of degree $n$ over $FF_p$ without a root, in the limit of large $p$: inclusion and exclusion over the roots gives $sum_(j <= n) (-1)^j binom(p, j) p^(-j) -> sum_(j<=n) (-1)^j slash j!$. So for large primes a polynomial with group $S_n$ behaves like a random polynomial.

#example(title: "The sieve as a Galois statistic")[
  @sec-short-galois reports, for 60 random strings of each length with digits up to 20, the share of primes between 200 and 20,000 modulo which $Q_s$ has no root. For $k = 3, 4, 5, 6$ the medians are 0.501, 0.335, 0.374 and 0.367, against $1/2, 1/3, 3/8, 11/30$. The local test of @thm-local therefore removes about $1 slash e$ of the strings per large prime, independently from prime to prime, which explains the speed of the sieve of @sec-search-short. Small primes are weaker, for a reason that has nothing to do with Galois theory: at $r equiv 1$ the polynomial reduces to the digit-sum identity of @thm-digit-sum (#lib("11.5")).
]

== Jordan's theorem and intersective polynomials <sec-app-galois-jordan>

Could a string pass the local test for every prime without being a solution anywhere? Jordan's theorem rules this out for irreducible polynomials.

#theorem(id: "app-galois-jordan", title: "Jordan", status: "cited")[
  A transitive group of permutations of $n >= 2$ points contains an element with no fixed point.
]

#proof[
  By Burnside's lemma, the average number of fixed points of an element of a transitive group is 1. The identity fixes $n >= 2$ points, more than the average. So some element fixes fewer than one point, that is none.
]

Cameron and Cohen @cameron-cohen1992 sharpened the count: at least a share $1 slash n$ of the elements of a transitive group fix no point. With Chebotarev this gives Proposition 12.1 of the library: if $Q_s$ is irreducible of degree $n$, it has no root modulo a set of primes of density at least $1 slash n$. Serre's survey @serre2003 gives the history and many applications.

For reducible polynomials the theorem can fail. A polynomial that has a root modulo every prime (or every integer), but no rational root, is called intersective.

#example(title: "An intersective polynomial")[
  $f(r) = (r^3 - 19)(r^2 + r + 1)$ has a root modulo every prime. For $p equiv 1 med (mod 3)$ the factor $r^2 + r + 1$ has a root, since $FF_p^*$ contains an element of order 3. For $p equiv 2 med (mod 3)$, cubing is a bijection of $FF_p$, so $r^3 = 19$ has a root. For $p = 3$ the root is $r = 1$, and for $p = 19$ it is $r = 0$. But $f$ has no rational root.
]

In Galois terms, the group of a product $g h$ acts on the roots of $g$ and of $h$ together, and an element can move every root of both factors even when each factor alone always keeps a root. The library proves that no Munchausen polynomial with $k <= 5$ is intersective without a rational root, and gives an exact criterion for $k = 6$: a quadratic and a cubic factor with the same quadratic field, the shape of the example above (#lib("16.3")). No such string is known. So in practice a string that passes every local test has a rational root, and the rational roots that are not bases are the "roots too small to be bases" of @sec-short-roots.

== Further reading <sec-app-galois-reading>

The Chebotarev theorem and its history are in @stevenhagen-lenstra1996. Jordan's original paper is @jordan1872, and @serre2003 surveys its descendants. Hilbert irreducibility is in @serre-topics2008. Ritt's decomposition theory starts with @ritt1922.
