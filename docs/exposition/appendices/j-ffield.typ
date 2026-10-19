#import "../template.typ": *

= Function fields over $FF_q$ <app-ffield>

The ring $FF_q [T]$ of polynomials over a finite field behaves in many ways like the integers. @sec-worlds-ffield uses it as a test world for Munchausen numbers: there the weights are additive, every structure can be computed exactly, and one can see precisely why the probabilistic model fails. This appendix gives the background. Rosen's book @rosen2002 develops the analogy between $FF_q [T]$ and $ZZ$ in depth.

== The ring $FF_q [T]$ <sec-app-ffield-ring>

Let $q$ be a prime (the library also allows prime powers) and $FF_q = ZZ slash q ZZ$. The ring $FF_q [T]$ has division with remainder by degree, so every ideal is principal and every nonzero polynomial factors uniquely into a constant times monic irreducible polynomials. These irreducibles play the role of primes. The degree measures size: put $|f| = q^(deg f)$, the number of residues modulo $f$. A polynomial of degree $e$ has $q^e$ residues, so it is the analogue of an integer of size $q^e$.

== Expansions in a polynomial base <sec-app-ffield-base>

Fix a base $B$ of degree $e >= 2$. The digits are the $q^e$ polynomials of degree less than $e$. Every polynomial $n$ has exactly one expansion $n = sum_i d_i B^i$ with digits $d_i$: take $d_0$ the remainder of $n$ modulo $B$ and repeat with $(n - d_0) slash B$.

The striking difference from the integers is that there are no carries. The sum of two digits has degree less than $e$, so it is again a digit, and the expansion of $n + n'$ is the digitwise sum. So the map from a polynomial to its digit vector is $FF_q$-linear.

== Frobenius <sec-app-ffield-frobenius>

#proposition(id: "app-ffield-frobenius", title: "Frobenius is additive")[
  In characteristic $q$, $(f + g)^q = f^q + g^q$ for all polynomials $f, g$. Since $c^q = c$ for every $c in FF_q$, also $f(T)^q = f(T^q)$.
]

#proof[
  In $(f + g)^q = sum_j binom(q, j) f^j g^(q - j)$, every middle binomial coefficient is divisible by the prime $q$. The second statement follows by applying the first to the monomials of $f$ and using Fermat's little theorem $c^q = c$.
]

So the weight that @sec-worlds-ffield gives a digit $d$ of degree $j$,
$ w(d) = d^(q^j) = d(T^(q^j)), $
the analogue of $x^x$ with the size $|d| = q^j$ as exponent, is additive on the digits of each degree. The Munchausen sum of $n$ therefore depends only on the sums $D_j$ of the digits of each degree $j$: $F(n) = sum_j D_j (T^(q^j)) + m z$, with $z$ the number of zero digits. The problem becomes finite and linear, up to the split of the digits into degree classes (#lib("21.1")).

== The block structure <sec-app-ffield-blocks>

Frobenius also acts on expansions in a simple way. If $n = sum_i d_i B^i$, then
$ n(T^q) = n^q = sum_i d_i^q (B^q)^i = sum_i d_i (T^q) B^(q i), $
and $d_i (T^q)$ has degree at most $(e - 1) q < q e$, so it has at most $q$ digits in base $B$. Each digit of $n$ becomes a block of $q$ digits of $n^q$, and the blocks do not overlap. Applied $j$ times, this shows that the digits of $F(n)$ are built from only $e$ digits, one for each degree class (Lemma 24.1 and Corollary 24.3 of #lib("24.2")). This rigid structure is what the probabilistic model, which treats the digits of $F$ as independent and uniform, cannot see.

#example(title: [A small base over $FF_2$])[
  Take $q = 2$ and $B = T^2 + T + 1$, so $e = 2$ and the digits are $0, 1, T, T + 1$. Their weights under $0^0 = 0$ are $w(0) = 0$, $w(1) = 1$, $w(T) = T^2$ and $w(T + 1) = (T + 1)^2 = T^2 + 1$. In characteristic 2, $T^2 = B + (T + 1)$, so $T^2$ has the digits $(1, T + 1)$, and its Munchausen sum is $w(1) + w(T + 1) = 1 + T^2 + 1 = T^2$. So $T^2$ is a solution. So is $T^2 + 1 = B + T$, with digits $(1, T)$ and sum $1 + T^2$. These are the $q (q - 1) = 2$ solutions that Theorem 21.7 predicts, since $B - 1 = T(T + 1)$ has two roots in $FF_2$ (@sec-worlds-ffield).

  The block structure shows in squares. Take $n = T^2 + 1$ with digits $(1, T)$. Squaring sends the digit $T$ to $T^2$, the block $(1, T + 1)$, and the digit 1 to the block $(0, 1)$. The blocks give $n^2$ the digits $(0, 1, 1, T + 1)$, and without the leading zero $n^2 = B^2 + B + (T + 1)$, which is indeed $T^4 + 1$.
]

== Traces and free residues <sec-app-ffield-trace>

Let $P$ be an irreducible polynomial of degree $f$. The residue ring $FF_q [T] slash (P)$ is a field with $q^f$ elements, and Frobenius $y |-> y^q$ is an automorphism of it of order $f$. The trace
$ "Tr"(y) = y + y^q + y^(q^2) + dots + y^(q^(f - 1)) $
is an $FF_q$-linear map onto $FF_q$, and $"Tr"(y^q) = "Tr"(y)$.

The digit-sum identity holds here too: $n equiv sum_i d_i med (mod B - 1)$, because $B equiv 1$. For a solution it reads $sum_j (D_j (T^(q^j)) - D_j) + m z equiv 0 med (mod B - 1)$. Reduce modulo an irreducible factor $P$ of $B - 1$ and apply the trace. Since $D_j (T^(q^j)) = D_j^(q^j)$ and the trace is invariant under Frobenius, every term $"Tr"(D_j (T^(q^j)) - D_j)$ vanishes. So under $0^0 = 0$ the identity holds for free on a subspace of codimension at least the number of irreducible factors of $B - 1$ (Theorem 21.6 of #lib("21.1")). In the integers the only such free residue is $x^x equiv x med (mod 2)$; here every prime factor of $B - 1$ gives one. This is why the count grows by a factor of about $q$ per factor of $B - 1$, the analogue of the parity doubling.

Under $0^0 = 1$ the constant $m z$ contributes the trace $z deg P$. If $deg P$ is prime to $q$, a solution needs $q | z$. Chapter 24 of the library turns this into an exact statement: when $B - 1$ has such a factor, the solutions under $0^0 = 1$ are the solutions under $0^0 = 0$ whose number of zero digits is divisible by $q$ (Proposition 24.11 of #lib("24.4")). Because the block structure forces many zeros, this share is far from what the model expects.

== Frobenius on $FF_q [T] slash (P^a)$ <sec-app-ffield-local>

The exact value of the free residue dimension $k(B)$ (@worlds-ff-kB) needs Frobenius on the whole ring $R = FF_q [T] slash (B - 1)$, not only on its residue fields. Write $B - 1 = product_i P_i^(a_i)$ with distinct monic irreducible $P_i$ of degree $f_i$. By the Chinese remainder theorem $R$ is the product of the local rings $R_i = FF_q [T] slash (P_i^(a_i))$, and Frobenius $phi(x) = x^q$ acts on each factor separately. It is $FF_q$-linear, because $(x + y)^q = x^q + y^q$ and $c^q = c$ for $c in FF_q$. Four facts about one local ring $R_i$ do all the work. Write $f = f_i$, $a = a_i$, and $L = FF_(q^f)$ for the residue field $R_i slash (P_i)$.

+ _Fixed points._ The solutions of $x^(q^j) = x$ in $R_i$ form a field with $q^(gcd(j, f))$ elements. Modulo $P_i$ they are the roots of $X^(q^j) - X$ in $L$, the subfield $FF_(q^(gcd(j, f)))$. Each such root lifts in exactly one way to $R_i$, by Hensel's lemma (@app-padic has the $p$-adic version), because the derivative of $X^(q^j) - X$ is $-1$ and never vanishes. In particular $phi - 1$ has a kernel of dimension 1 on each $R_i$, and of dimension $omega(B - 1)$ on $R$. This is the starting point of Berlekamp's factoring algorithm.
+ _The nilradical._ The multiples of $P_i$ form the nilradical $N$ of $R_i$: each of them has $x^a = 0$. Frobenius is nilpotent on $N$, since $x^(q^r) = 0$ once $q^r >= a$. So $phi^j - 1$ is invertible on $N$, and the image of $phi^j - 1$ on $R_i$ contains $N$. It is the set of elements whose reduction lies in the image of $phi^j - 1$ on the field $L$.
+ _The image on the field._ On $L$, with $K = FF_(q^g)$ and $g = gcd(j, f)$, the image of $phi^j - 1$ is the kernel of the trace from $L$ to $K$. The image lies in that kernel because the trace is invariant under $phi^j$. Both have dimension $f - g$ over $FF_q$, since the kernel of $phi^j - 1$ is $K$. This is the additive form of Hilbert's theorem 90.
+ _Sums of images._ If a set $S$ of exponents $j$ has $gcd(S union {f}) = 1$, then the images of $phi^j - 1$ for $j in S$ add up to the image of $phi - 1$, the kernel of the trace from $L$ to $FF_q$. Under the trace form $(x, y) |-> "Tr"_(L slash FF_q)(x y)$, the kernel of the trace to $K$ is the orthogonal complement of $K$. So the sum of the images is the orthogonal complement of the intersection of the fields $FF_(q^(gcd(j, f)))$, which is $FF_q$.

Two exponents $j$ and $j + 1$ always satisfy the condition of fact 4, and so does $j = e - 1$ when $gcd(e - 1, f) = 1$. These are the two cases that the proof of @worlds-ff-kB uses.
