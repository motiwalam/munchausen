#import "../template.typ": *

= The probabilistic model <ch-model>

The constructions of @ch-constructions explain a few solutions, mostly short ones and mostly in special bases. The long solutions near $b$ digits show no structure at all. This chapter treats them as coincidences. A digit multiset has some small chance to reproduce itself, and the chance can be computed. The resulting model predicts how many solutions a base has, how long they are, and why odd bases have more of them. It survives every test the library has tried on it, with one exception in the factorial number system and one in function fields (@sec-worlds-factorial, @sec-worlds-ffield).

Two warnings before we start. First, everything in this chapter marked "heuristic" is a statement about a random model, not about $x^x$. The model is tested against data, and the tests are the evidence. Second, the data are small: a few dozen bases with one or two solutions each. So the chapter often asks whether a deviation is chance. The answer depends on how the question was chosen, a point that @sec-model-anomalies explains.

== The counts per base <sec-model-data>

The exhaustive search of @ch-search has found every solution in bases 2 to 41 and in base 43, under both conventions. The full table is in @sec-basics-data and @app-tables. Here are the facts that the model must explain.

- Most bases have one to three nontrivial solutions under each convention. The largest count up to base 43 is 7, in base 15 under $0^0 = 0$.
- The longest solution usually has $b - 1$ digits: in 23 of the 29 bases from 10 to 41 that have a solution #lib("4.3"). Only bases 15 and 16 have a $b$-digit solution, both under $0^0 = 0$.
- Odd bases have more solutions under $0^0 = 0$. Over bases 10 to 41, odd bases average 2.56 solutions and even bases 1.56. Under $0^0 = 1$ the averages are 1.81 and 1.69 #lib("4.3").
- The counts of the two conventions are correlated, 0.56 over bases 10 to 41. A solution without the digit 0 counts under both conventions (@thm-conventions), and 35 of the 56 solutions under $0^0 = 1$ in these bases are zero-free.
- Bases 19, 27 and 35 have no solution under either convention. They are the only empty bases from 3 to 41, and base 43 has solutions.

If each base had a Poisson number of solutions with the mean of the refined model of @sec-model-refined, bases 10 to 39 would show the distribution of @tab-model-poisson-shape. The counts follow the Poisson shape roughly. The upper tail is heavier, because twins and constructed solutions come in groups and small bases have extra solutions.

#tablefig(caption: [Bases 10 to 39 with exactly $n$ nontrivial solutions, observed against a Poisson law with the mean of the refined model #lib("4.4").], id: "tab-model-poisson-shape")[
  #btable(columns: 8, align: (left,) + (right,) * 7,
    [], [$n = 0$], [1], [2], [3], [4], [5], [6+],
    [$0^0 = 0$, expected], [6.3], [8.9], [7.1], [4.2], [2.1], [0.9], [0.4],
    [$0^0 = 0$, observed], [6], [9], [5], [3], [3], [3], [1],
    [$0^0 = 1$, expected], [8.6], [10.7], [6.7], [2.8], [0.9], [0.2], [0.1],
    [$0^0 = 1$, observed], [6], [7], [9], [4], [3], [1], [0],
  )
]

Some counts are forced by structure. Under $0^0 = 0$ solutions ending in 0 or 1 come in twins (@thm-twins), so $N_0 (b)$ has the parity of the number of solutions whose last digit is at least 2. Bases with self-paying digits always have solutions under $0^0 = 0$ (@thm-structure-m0), and the count is unbounded along special bases (@thm-many-m0). The model ignores all of this. It describes the generic coincidences, and it should be compared with the data after the families are set aside or in large bases where they are rare.

== The basic model and the large-base limit <sec-model-basic>

Fix a length $k$ and a digit multiset $c$ with $k$ digits. Its weight $S(c) = sum_x c_x w(x)$ is one fixed number. The multiset gives a solution exactly when the base-$b$ digits of $S(c)$ form the multiset $c$. The model replaces the digits of $S(c)$ by random digits.

#definition(id: "model-def-basic", title: "Basic model", src: "5.1")[
  For each multiset $c$ of $k$ digits, the digits of $S(c)$ are drawn uniformly among the $k$-digit strings with a nonzero leading digit, independently for different multisets. The multiset is a _model solution_ if the drawn string has the multiset $c$.
]

The chance that a random $k$-digit string has a given multiset $c$ is the same for the drawn string as for a random string $n$. Summing over all multisets $c$ whose weight has $k$ digits gives a formula that is easy to estimate by sampling.

#proposition(id: "model-prop-ek", title: "Expected count per length", src: "5.1")[
  In the basic model, the expected number of $k$-digit solutions is
  $ E_k = P(F(n) "has exactly" k "digits"), $
  where $n$ is a uniform random $k$-digit number.
]
#proof[
  Let $p(c)$ be the probability that a uniform $k$-digit string has multiset $c$. A multiset $c$ whose weight has $k$ digits is a model solution with probability $p(c)$, and one whose weight has another length is never one. So the expected count is the sum of $p(c)$ over the multisets with $k$-digit weight. That is the probability that a uniform $n$ has such a multiset, and $F(n) = S(c)$.
]

The formula says something striking. Sum over all lengths. The events "$F(n)$ has $k$ digits" for a $k$-digit random $n$ are different events for different $k$, but in a large base they behave like a partition of one event. So the expected total is close to 1.

Let $b$ grow with $J = b - k$ fixed. The digit counts of a random $k$-digit string become independent Poisson variables with mean $k slash b -> 1$. A digit $b - y$ weighs
$ (b - y)^(b - y) = b^(b-y) (1 - y slash b)^(b-y) approx e^(-y) b^(b - y), $
so the largest digit present decides the length of $F(n)$. One copy of $b - 1$ weighs about $b^(b-1) slash e$, so $c$ copies give $F approx (c slash e) b^(b-1)$. This crosses $b^(b-1)$, the smallest $b$-digit number, when $c >= 3$.

#heuristic(id: "heur-length-law", title: "The length law", src: ("5.2", "10.5"))[
  In the large-base limit a base has on average one solution per convention before the parity effect of @sec-model-refined. Its length is $b$, $b - 1$, $b - 2$, $b - 3$, $b - 4$ with probabilities about 8.0%, 55.2%, 23.2%, 8.6%, 3.2%, and each further digit of shortfall costs a factor of about $e$. The expected number of solutions with $J = b - k >= j$ is about $e^(-(j-1))$ for $j >= 1$.
]
#sketch[
  The cases are disjoint and cover almost everything. Write $c_x$ for the Poisson(1) counts.
  - $k = b$: the sum needs at least $b$ digits, so at least 3 copies of $b - 1$. The probability is $P("Poisson"(1) >= 3) = 1 - (5 slash 2) e^(-1) = 0.080$.
  - $k = b - 1$: one or two copies of $b - 1$ put $F$ between $b^(b-2)$ and $b^(b-1)$, with probability $(3 slash 2) e^(-1) = 0.552$.
  - $k = b - j$ for $j >= 2$: no digit above $b - j$ and at least one copy of $b - j$. This has probability $e^(-(j-1)) (1 - e^(-1))$, which gives 0.233, 0.086, 0.032 for $j = 2, 3, 4$.
  The five numbers add up to 0.983, and the tail adds the rest to 1. In each case the event "$F(n)$ has $k$ digits" has the stated probability, and @model-prop-ek turns it into the expected count. The third case is slightly loose: more than $e^j$ copies of $b - j$ push $F$ up one length, and more than $e^(j+1)$ copies of $b - j - 1$ push it up to $b - j$ digits. These rare cases move the shares by less than $10^(-5)$. @thm-length-shares below uses the exact events.
]

The law holds well at finite $b$. @tab-model-length-law shows the exact model at bases 50 to 800 #lib("10.5"). For $J$ up to about $ln b$ the values match the limit. Beyond that they are about three times the limit, a bump that @sec-model-window explains.

#tablefig(caption: [Expected number of solutions with $J = b - k$ in the basic model #lib("10.5").], id: "tab-model-length-law")[
  #btable(columns: 6, align: (right,) * 6,
    [$J$], [base 50], [base 100], [base 200], [base 800], [limit],
    [0], [0.078], [0.080], [0.081], [0.078], [0.080],
    [1], [0.554], [0.554], [0.546], [0.553], [0.552],
    [2], [0.237], [0.234], [0.233], [0.231], [0.233],
    [4], [0.036], [0.034], [0.033], [0.031], [0.032],
    [8], [0.0029], [0.0021], [0.0018], [0.0010], [0.0006],
    [12], [0.00030], [0.00009], [0.00002], [0.00003], [0.00001],
  )
]

#remark(id: "model-rem-universal-one")[
  The total of 1 does not depend on the details of $x^x$. It only needs the length of $F(n)$ to be nearly independent of the length of $n$ near the critical length, so that $sum_k P(ell(F_k) = k)$ is close to $sum_ell P(ell(F) = ell) = 1$. This is why "about one solution per base" holds in every number system of @ch-worlds where digits can move freely. The length shares, in contrast, depend on how high the top weight sits between two powers of the base, and they change from system to system (@sec-worlds-universal).
]

=== The length shares are a theorem in the model <sec-model-shares>

The sketch of @heur-length-law replaces the digit counts by independent Poisson variables and the weights by their limits. Both steps can be made exact, so in the basic model the shares are a theorem about random strings. Whether real bases follow the model is a separate question; the heuristic label of @heur-length-law refers to that.

Fix $j >= 0$. For $y >= 1$ let $gamma(y) = (e^y - floor(e^y)) slash e^y$. It is positive because $e^y$ is not an integer, and it measures how far $e^y$ is from the integer below it. Let $gamma_j$ be the smaller of $gamma(j)$ and $gamma(j + 1)$ (only $gamma(1)$ when $j = 0$). Write $N_x$ for the number of copies of the value $x$ in a random string and $y_0$ for the distance of the largest digit from $b$, so that the largest digit is $b - y_0$. The limit share is
$ s_j = sum_(1 <= k < e^j) e^(-j) / k! + sum_(k > e^(j+1)) e^(-(j+1)) / k! . $
The first sum is "the largest digit is $b - j$, with fewer than $e^j$ copies". The second is "the largest digit is $b - j - 1$, with more than $e^(j+1)$ copies"; it adds $3.8 dot 10^(-6)$ to $s_1$ and less elsewhere. So $s_0 = e^(-1) (e - 5 slash 2)$, and $s_0, dots, s_5$ are 0.0803, 0.5518, 0.2325, 0.0855, 0.0315, 0.0116.

The proof has three steps. The first makes the weights precise.

#lemma(id: "model-lem-weights", title: "Top weights", src: "29.1")[
  For $0 <= y < b$,
  $ e^(-y) b^(b-y) <= (b - y)^(b - y) <= e^(-y) b^(b-y) exp(y^2 / (2(b - y))). $
]
#proof[
  Put $t = y slash b$. Then $ln (b-y)^(b-y) - (b - y) ln b = b (1 - t) ln(1 - t)$, and $(1 - t) ln(1 - t) = -t + sum_(k >= 2) t^k slash (k(k-1))$, a series whose terms after the first are positive. So the left side is at least $-y$, and at most $-y + (y^2 slash 2b) sum_(m >= 0) t^m = -y + y^2 slash (2(b - y))$.
]

The second step compares the top counts with Poisson variables. It uses the total variation distance of @app-prob-def-tv and the coupling of @sec-app-prob-coupling.

#lemma(id: "model-lem-coupling", title: "Poisson coupling of the top counts", src: "29.1")[
  Let $d = b - j$ and $K = j + 1$. The vector $(N_(b-1), dots, N_(b-K))$ of a random $d$-digit string is within total variation distance $((j + 1)^2 + 1) slash b$ of $K$ independent Poisson(1) variables.
]
#sketch[
  Replacing the leading digit by a uniform digit costs $1 slash b$. For $d$ uniform digits, given the total of the $K$ counts, the counts are multinomial with equal cells, and so are independent Poisson variables given their total. So only the totals need to be compared: a binomial total against a Poisson total costs at most $K slash b$ by @app-prob-barbour-hall, and moving the Poisson mean from $d K slash b$ to $K$ costs at most $1 - e^(-K j slash b) <= K j slash b$.
]

The third step shows that the length of $F(n)$ depends only on these counts, unless some top value occurs more than $sqrt(b)$ times, which is very unlikely.

#theorem(id: "thm-length-shares", title: "Length shares in the basic model", src: ("29.1", "13.2"))[
  Fix $j >= 0$ and let $b_0(j) = max(e^(j+2), j + 1 + 2(j+1)^2 slash gamma_j, 64 slash gamma_j^2)$. For every base $b >= b_0(j)$, under either convention, the expected number $E_(b-j)(b)$ of $(b - j)$-digit solutions in the basic model satisfies
  $ |E_(b-j)(b) - s_j| <= ((j + 1)^2 + 1) / b + (j + 2) / (floor(sqrt(b)))! . $
  In particular $E_(b-j)(b) -> s_j$.
]
#sketch[
  Let $M = floor(sqrt(b))$ and let $H$ be the event that each of the values $b - 1, dots, b - j - 2$ occurs at most $M$ times. A value occurs more than $M$ times with probability at most $1 slash M!$, so $P("not" H) <= (j + 2) slash M!$. Suppose $H$ holds and the largest digit is $b - y$ with $k$ copies, $y in {j, j + 1}$. By @model-lem-weights, $F slash b^(b-y)$ lies between $k e^(-y)$ and $k e^(-y)$ times a factor close to 1, plus at most $(M + 2) slash b$ for the lower digits. The condition $b >= b_0(j)$ keeps all these error terms below $gamma_j$, the gap between $k e^(-y)$ and 1. So $F$ has $b - y + 1$ digits if $k > e^y$ and $b - y$ digits if $k < e^y$. A largest digit above $b - j$ makes $F$ too long, and one below $b - j - 1$ makes it too short. So on $H$ the event "$F$ has $b - j$ digits" depends only on the top $j + 1$ counts, and under independent Poisson(1) counts its probability is exactly $s_j$, because $P(y_0 = y, N_(b-y) = k) = e^(-y) slash k!$. @model-lem-coupling bounds the change from the true counts to the Poisson ones.
]

The constant $b_0(j)$ is crude: $b_0(0) = 919$ and $b_0(1) = 23,000$. It only keeps the threshold $e^y$ away from the integers. The exact values below show the convergence already at base 30.

#corollary(id: "model-cor-total", title: "One solution per base", src: "29.1")[
  In the basic model, $sum_(d = 1)^b E_d (b) -> 1$ as $b -> infinity$, and the share of the length $b - j$ tends to $s_j$.
]
#sketch[
  The events of @thm-length-shares for $j = 0, 1, 2, dots$ split the Poisson outcomes, so $sum_j s_j = 1$. For the tail, on the event that $F$ has $b - j$ digits every digit $x$ satisfies $x^x < b^(b-j)$, which forces $x < b - 0.75 j$ for $b >= 21$. Each of the about $b$ digits must avoid $0.75 j - 1$ values, so the share of the lengths with $J <= j <= b slash 2$ is at most $5.6 e^(-J slash 3)$. The lengths below $b slash 2$ contribute $O(1 slash sqrt(b))$, because then every digit is below $max(2 d, sqrt(b))$. Let $b$ and then $J$ tend to infinity.
]

#computation(id: "model-comp-shares", title: "The shares at finite bases", src: "29.1")[
  Exact values of $E_(b-j)(b)$ from the law of the top counts, and the scaled error $b (E_(b-j) - s_j)$:
  #align(center, btable(columns: 6, align: (right,) * 5 + (left,),
    [$b$], [$E_b$], [$E_(b-1)$], [$E_(b-2)$], [$E_(b-3)$], [$b(E - s)$ for $j = 0, 1, 2, 3$],
    [30], [0.07735], [0.55501], [0.24203], [0.09693], [$-0.089, +0.096, +0.285, +0.341$],
    [100], [0.07939], [0.55275], [0.23536], [0.08879], [$-0.091, +0.093, +0.282, +0.324$],
    [1000], [0.08021], [0.55191], [0.23282], [0.08587], [$-0.092, +0.092, +0.281, +0.318$],
    [100000], [0.08030], [0.55182], [0.23254], [0.08555], [$-0.092, +0.092, +0.281, +0.317$],
  ))
  A Monte Carlo of the model program itself agrees within 1.5 standard errors at bases 30 and 100.
]

The last column converges, so the error is $c_j slash b$ to first order. The library computes the constants exactly: $E_(b-j)(b) = s_j + c_j slash b + O(1 slash b^2)$ with $c_0 = -1 slash (4 e) = -0.092$ and $c_1, dots, c_5 = 0.092, 0.281, 0.317, 0.227, 0.136$ (Proposition 29.7 of #lib("29.1")). The base-100 numbers of @model-heur-base100 are these values. Every later use of "about one solution per base" in the basic model rests on @model-cor-total.

=== The expected count is a trace <sec-model-trace>

The shares and their total of 1 have a compact form in the language of
matrices. Let $M_b$ be the $b times b$ matrix whose entry $M_b (d, d')$ is
the chance that $F(n)$ has $d'$ digits when $n$ is a uniform $d$-digit
string. A multiset with at most $b$ digits has $F < b^b$
(@model-prop-cycles), so $F(n)$ has between 1 and $b$ digits, and every row
of $M_b$ is a probability law. So $M_b$ is a stochastic matrix
(@sec-app-prob-stochastic). Its diagonal entry $M_b (d, d)$ is $E_d$ of
@model-prop-ek.

#proposition(id: "model-prop-trace", title: "The count is a trace", src: "34.3")[
  The expected count of the basic model over the lengths 2 to $b$ is
  $"tr" M_b - M_b (1, 1)$. The first entry is
  $M_b (1, 1) = E_1 = N_1 (b) slash (b - 1)$, where $N_1 (b)$ is the number
  of digits $x >= 1$ with $x^x < b$. So $N_1 (b) = 2$ for
  $5 <= b <= 27$, 3 for $28 <= b <= 256$ and 4 for $257 <= b <= 3125$.
]
#proof[
  The diagonal entries are the $E_d$, and the count over the lengths 2 to
  $b$ is their sum without $E_1$. A 1-digit string $x$ has $F = x^x$, which
  has one digit exactly when $x^x < b$, and $x$ is uniform on
  $1, dots, b - 1$.
]

Length 1 is an artefact of the model: whatever $E_1$ says, the only
1-digit number with $n = F(n)$ is the trivial $n = 1$. So the library
counts from length 2. The entry $E_1$ is also almost an
eigenvalue of $M_b$, because a string of length $d >= 2$ has $F < b$ only
if all its digits are tiny. At $b = 100$ the eigenvalue is 0.0312 against
$E_1 = 0.0303$. A first computation that kept length 1 found a second
eigenvalue "about $3 slash b$". That was this entry, with $N_1 = 3$
#lib("34.3").

The theorem on the shares separates into rows and columns.

#theorem(id: "model-thm-rows", title: "The rows converge", src: "34.3")[
  Fix $j, j' >= 0$. For every base $b >= b_0 (j')$, the constant of
  @thm-length-shares,
  $ |M_b (b - j, b - j') - s_(j')| <= ((j + 1)(j' + 1) + 1) / b + (j' + 2) / (floor(sqrt(b)))! . $
  So for each fixed $J$, the $J times J$ corner of $M_b$ at the longest
  lengths tends to the matrix whose rows all equal $(s_0, dots, s_(J-1))$.
]
#sketch[
  This is the proof of @thm-length-shares with the row and the column kept
  apart. The column $b - j'$ decides which event counts: on the event $H$
  the length $b - j'$ depends only on the top $j' + 1$ counts. The row
  $b - j$ enters only through the coupling of @model-lem-coupling, applied
  to the top $K = j' + 1$ counts of a string of $b - j$ digits, which costs
  $(1 + K + K j) slash b$. Under the Poisson law the chance of the event is
  $s_(j')$, whatever $j$ is.
]

#corollary(id: "model-cor-rows", title: "One law for every row", src: "34.3")[
  For each fixed $j$, the law of the length of $F(n)$, for $n$ a uniform
  string of $b - j$ digits, tends to the law $(s_0, s_1, dots)$ at the
  distances $0, 1, dots$ from $b$. The shares $s_j$ of @thm-length-shares
  are the diagonal of this limit, and they add to 1 because the limit is a
  probability law.
]

In the language of @sec-app-prob-stochastic, the corner of $M_b$ is close
to a matrix with equal rows, whose trace is 1. That is the reason behind
"about one solution per base" (@model-rem-universal-one): the length of
$F(n)$ barely depends on the length of $n$.

How far is the trace from 1 at a finite base? A string with $b - j$ digits
has on average $(b - j - 1) slash b$ copies of each value among its free
digits, a little fewer than 1, and fewer for shorter strings. So its top
counts behave like Poisson variables with mean $mu approx 1 - (j + 1) slash b$
in place of 1. Write $s_(j') (mu)$ for the share of the length $b - j'$
when the top counts are independent Poisson($mu$) variables, and
$sigma_(j') = -s'_(j') (1)$ for minus its derivative at $mu = 1$.

#proposition(id: "model-prop-first-order", title: "The first correction to the trace", src: "34.3")[
  For fixed $j$ and $j'$,
  $ M_b (b - j, b - j') = s_(j') + ((j + 1) sigma_(j') + a_(j')) / b + O(1 / b^2), $
  where $a_(j')$ does not depend on $j$. Both $sigma_(j')$ and $a_(j')$ sum
  to 0 over $j'$. For every fixed $J$, the diagonal satisfies
  $ sum_(j < J) M_b (b - j, b - j) = sum_(j < J) s_j + 1 / b sum_(j < J) c_j + O_J (1 / b^2), quad c_j = (j + 1) sigma_j + a_j . $
  The sum of all the $c_j$ is
  $ C = sum_j c_j = - d / (d mu) E_mu [J'] |_(mu = 1) = e / (e - 1)^2 + 1 / (2 e) + 2.2 dot 10^(-5) = 1.104636, $
  where $J'$ is the distance of the length of $F$ from $b$ when the top
  counts are independent Poisson($mu$) variables.
]
#sketch[
  The term $(j + 1) sigma_(j') slash b$ is the first-order change of
  $s_(j') (mu)$ when $mu$ moves from 1 to $1 - (j + 1) slash b$. The term
  $a_(j') slash b$ collects the leading digit, the step from binomial to
  Poisson counts and the correction of @model-lem-weights, none of which
  depends on $j$. Since $sum_(j') s_(j') (mu) = 1$ for every $mu$, the
  $sigma_(j')$ sum to 0, and since the rows of $M_b$ sum to 1, so do the
  $a_(j')$. Summing the diagonal over all $j$ gives
  $sum_j ((j + 1) sigma_j + a_j) = sum_j j sigma_j = -d slash d mu sum_j j s_j (mu)$,
  minus the derivative of the mean of $J'$. For the closed form, the
  distance $y_0$ of the largest digit from $b$ has
  $P(y_0 = y) = e^(-mu (y - 1)) (1 - e^(-mu))$, so
  $E_mu [y_0] = 1 slash (1 - e^(-mu))$, whose derivative at 1 is
  $-e slash (e - 1)^2$. The length is one more than $b - y_0$ when the
  largest digit has more than $e^(y_0)$ copies, and this adds the small
  terms $1 slash (2 e)$ (from $y_0 = 1$) and $2.2 dot 10^(-5)$.
]

The proposition is proved for each fixed $J$. Letting $J$ grow with $b$
needs a bound on $E_(b-j) - s_j - c_j slash b$ that is uniform in $j$,
which is open (#q(141)). The tail bound in the proof of @model-cor-total
is not small enough. A computation closes the gap. It also shows that the
whole first-order excess is a single eigenvalue.

#heuristic(id: "model-heur-one-eigen", title: "One eigenvalue carries the excess", src: "34.3")[
  To first order the corner of $M_b$ is $bold(1) u^T + (1 slash b) v sigma^T$
  with $u = s + a slash b$ and $v_j = j + 1$. By @sec-app-prob-stochastic its
  eigenvalues are 1, $(sigma dot v) slash b = C slash b$ and zeros. So
  $"tr" M_b - E_1 = 1 + C slash b + o(1 slash b)$, and the excess over 1 is
  one eigenvalue, $lambda_2 approx C slash b$.
]

#computation(id: "model-comp-trace", title: "Trace and second eigenvalue", src: "34.3")[
  The exact length matrix (both conventions agree to 6 digits). The last
  column is $b lambda_2$ for the matrix restricted to the lengths
  $2, dots, b$:
  #align(center, btable(columns: 5, align: (right,) * 5,
    [$b$], [$"tr" M_b$], [$E_1$], [$b("tr" M_b - E_1 - 1)$], [$b lambda_2$],
    [10], [1.5417], [0.2222], [3.195], [2.30],
    [20], [1.2676], [0.1053], [3.246], [1.52],
    [40], [1.1236], [0.0769], [1.869], [1.34],
    [100], [1.0448], [0.0303], [1.446], [1.20],
    [200], [1.0214], [0.0151], [1.260], [1.14],
    [300], [1.0175], [0.0134], [1.229], [1.14],
  ))
]

Both columns approach $C = 1.105$. At small bases the shorter lengths add
more, which is why the excess at base 20 is about 3 times $C slash b$. The
constant has a plain meaning: it measures how much the length of $F$
follows the length of the string. A string with one digit fewer has fewer
large digits, so its $F$ tends to be a little shorter too, and the diagonal
gains. With length 1 included, the trace is
$1 + (N_1 (b) b slash (b - 1) + C) slash b + o(1 slash b)$, so
$b ("tr" M_b - 1)$ grows like $ln b slash ln ln b$ and has no limit.

== The digit-sum identity and the parity effect <sec-model-refined>

The basic model forgets one fact. Every integer satisfies $n equiv (text("digit sum of") n) med (mod b - 1)$, because $b equiv 1$. For a solution this becomes the identity of @thm-digit-sum: the multiset must satisfy $sum_x c_x (w(x) - x) equiv 0 med (mod b - 1)$.

#definition(id: "model-def-refined", title: "Refined model", src: "5.3")[
  The digits of $S(c)$ are drawn uniformly among the $k$-digit strings whose digit sum is congruent to $S(c)$ modulo $b - 1$.
]

A multiset that meets the identity becomes $b - 1$ times as likely to be a solution, and a multiset that fails it becomes impossible. On average nothing changes, unless the identity holds more often than one time in $b - 1$. It does, because of the prime 2.

#heuristic(id: "model-heur-parity", title: "Parity factors", src: ("5.3", "17.3"))[
  In the large-base limit the refined model multiplies the expected count of the basic model by these factors:
  #align(center, btable(columns: 3, align: (left, right, right),
    [], [even base], [odd base],
    [$0^0 = 0$], [1], [2],
    [$0^0 = 1$], [1], [$1 + e^(-2) approx 1.135$],
  ))
  More generally, with $w(0) = m$, the odd-base factor is 2 for even $m$ and $1 + e^(-2)$ for odd $m$.
]
#sketch[
  For every $x >= 1$, $x^x equiv x med (mod 2)$. In an odd base $b - 1$ is even. Under $0^0 = 0$ every term $w(x) - x$ is then even, so the identity holds modulo the 2-part of $b - 1$ for every multiset. Modulo the odd part it holds with the usual chance. So the share of multisets that meet the identity is twice the random share, and the count doubles. Under $0^0 = 1$ a zero contributes $1 - 0 = 1$, so the identity modulo 2 says that the number of zeros is even. The zero count is close to Poisson(1), and $P("Poisson"(1) "even") = (1 + e^(-2)) slash 2$. Twice that is the factor. For an odd prime $p$ dividing $b - 1$, the residues of $x^x - x$ modulo $p$ are spread, and a sum of about $b$ of them is close to uniform, so the factor is 1. In an even base $b - 1$ is odd and nothing changes.
]

So a large odd base expects two solutions under $0^0 = 0$ and about 1.135 under $0^0 = 1$, and a large even base expects one under each. Averaged over all bases, the model predicts 1.5 solutions per base under $0^0 = 0$ and about 1.07 under $0^0 = 1$ #lib("7.4").

The factor 1 for odd primes is the one assumption of this section that is not obvious. It says that the residues of $x^x$ modulo the odd prime powers in $b - 1$ spread evenly over the multisets whose weight has the right length. @sec-model-poisson calls it Assumption R. It reduces to one exponential sum per base, which a computation bounds for every base up to 6000; beyond that it is open (@sec-model-assumption-r). A weaker form, enough for the Poisson law in the limit, holds in every base (@sec-model-anticonc). For 2-digit narcissistic numbers the doubling of odd bases is a theorem (@worlds-narc-parity).

=== The refined count as a sum over characters <sec-model-characters>

The refined model has a trace form too, and it shows where the parity
factors come from. Put $q = b - 1$ and use the additive characters
$e(t) = e^(2 pi i t)$ of @sec-model-assumption-r. For a residue $t$ modulo
$q$ let
$ tau_t (b) = sum_(d = 2)^b E[bold(1){F(n) "has" d "digits"} e(t (F(n) - n) / q)], $
with $n$ a uniform $d$-digit string in each term.

#proposition(id: "model-prop-characters", title: "A sum over characters", src: "34.3")[
  The expected count of the refined model over the lengths 2 to $b$ is
  $sum_(t mod q) tau_t (b)$. The term $t = 0$ is the basic count
  $"tr" M_b - E_1$.
]
#proof[
  The $d$-digit numbers are $q b^(d - 1)$ consecutive integers, so $n$ is
  exactly uniform modulo $q$. Since $n$ is congruent to its digit sum, a
  multiset meets the identity of @thm-digit-sum exactly when
  $F(n) equiv n med (mod q)$, and the refined model makes such a multiset
  $q$ times as likely. So the refined count of length $d$ is
  $q P(F(n) "has" d "digits and" F(n) equiv n)$. The indicator of
  $F(n) - n equiv 0$ is $(1 slash q) sum_t e(t (F(n) - n) slash q)$. Take
  expectations and sum over $d$.
]

The term $t = 0$ counts every multiset with the right length, as the basic
model does. The other terms correct for the residue. For odd $b$ the
character with $t = q slash 2$ is $e(m slash 2) = (-1)^m$, a parity, and
there the prime 2 acts exactly.

#corollary(id: "model-cor-two-blocks", title: "Two closed classes", src: ("34.3", "15.1"))[
  For odd $b$ under $0^0 = 0$, $tau_(q slash 2) (b) = tau_0 (b)$ exactly.
  The matrix of the classes (length, residue modulo $q$) splits into two
  closed blocks, the even and the odd numbers, so its eigenvalue 1 has
  multiplicity 2. The refined count is $2 tau_0$ plus the other
  characters. This is the only case in which a character other than
  $t = 0$ is constant on $F(n) - n$.
]
#proof[
  For odd $b$, $n$ is congruent to its digit sum modulo 2, and
  $x^x equiv x med (mod 2)$ for $x >= 1$. So under $0^0 = 0$ the number
  $F(n) - n$ is always even, and $(-1)^(F(n) - n) = 1$. The last sentence
  is the theorem of the library on invariant residues #lib("15.1").
]

#theorem(id: "model-thm-e2", title: [The character of order 2 under $0^0 = 1$], src: "34.3")[
  For odd $b$ under $0^0 = 1$, $tau_(q slash 2) (b) -> e^(-2)$ as
  $b -> infinity$.
]
#sketch[
  Now $F(n) - n equiv z(n) med (mod 2)$, where $z(n)$ is the number of
  zeros, so $tau_(q slash 2) = sum_d E[bold(1){F "has" d "digits"} (-1)^(z(n))]$.
  For $d = b - j$ with $j$ fixed, the length event depends only on the top
  counts (@thm-length-shares). The coupling of @model-lem-coupling, with
  the count of zeros as one more coordinate, makes all these counts
  independent Poisson(1) variables up to an error $O(1 slash b)$. Under
  that law the zeros are independent of the length, and
  $E[(-1)^Z] = e^(-2)$ for $Z$ Poisson(1). So the term of length $b - j$
  tends to $e^(-2) s_j$. The tail bound of @model-cor-total handles the
  other lengths, and $sum_j s_j = 1$.
]

So the factor $1 + e^(-2)$ of @model-heur-parity is, in the model, a
theorem about one character. The factor 2 is @model-cor-two-blocks, and an
even base has no character of order 2. What is left is the claim that the remaining characters
contribute nothing in the limit.

#conjecture(id: "model-conj-characters", title: "The other characters vanish", src: "34.3")[
  $sum_(t in.not {0, q slash 2}) tau_t (b) -> 0$ as $b -> infinity$. Then
  the refined count tends to 1 in even bases, to 2 in odd bases under
  $0^0 = 0$ and to $1 + e^(-2)$ in odd bases under $0^0 = 1$.
]

This needs the sums $sum (x^x - x)$ to be equidistributed modulo $q$ with a
small relative error, a strong form of Assumption R. The anti-concentration
of @sec-model-anticonc gives only an upper bound for each residue, which is
not enough.

#computation(id: "model-comp-characters", title: "The characters at finite bases", src: "34.3")[
  The refined count over the lengths 2 to $b$, split by characters:
  #align(center, btable(columns: 6, align: (right,) * 6,
    [$b$], [$0^0$], [refined], [$tau_0$], [$tau_(q slash 2)$], [other characters],
    [13], [0], [2.892], [1.265], [1.265], [$+0.362$],
    [13], [1], [1.731], [1.265], [0.267], [$+0.200$],
    [25], [0], [2.404], [1.107], [1.107], [$+0.191$],
    [31], [1], [1.228], [1.071], [0.172], [$-0.015$],
    [63], [1], [1.166], [1.026], [0.149], [$-0.009$],
    [64], [0], [1.087], [1.025], [], [$+0.062$],
    [100], [0], [1.014], [1.015], [], [$-0.001$],
  ))
  Over the bases 10 to 64 the other characters add $-0.23$ to $+0.36$,
  and at most 0.11 in absolute value for $25 < b <= 128$. Under
  $0^0 = 1$ the ratio $tau_(q slash 2) slash tau_0$ is 0.211 at $b = 13$
  and 0.145 at $b = 63$, close to $(1 - 2 slash b)^(b - 2)$, which tends to
  $e^(-2) = 0.135$.
]

The largest contributions of the other characters come at $b$ = 13, 11,
25, 22, 29, 14, 37 and 43, with no simple rule yet (#q(142)).

=== The model against the data

#computation(id: "model-comp-totals", title: "Totals in bases 10 to 38", src: "5.4")[
  Nontrivial solutions in bases 10 to 38, summed over all lengths:
  #align(center, btable(columns: 5, align: (left, left, right, right, right),
    [convention], [bases], [basic model], [refined model], [observed],
    [$0^0 = 0$], [even], [17.2], [17.3], [22],
    [$0^0 = 0$], [odd], [16.0], [32.5], [38],
    [$0^0 = 1$], [even], [17.2], [17.4], [26],
    [$0^0 = 1$], [odd], [16.0], [19.1], [26],
  ))
]

The refined model explains the large difference between odd and even bases under $0^0 = 0$: the basic model predicts the same for both, the data show nearly twice as many in odd bases (38 against 22), and the refined model predicts a factor of 1.88. The remaining surplus sits in small bases, which contain the algebraic families of @ch-constructions. For bases 20 to 38 under $0^0 = 1$ the basic model expects 20.6 and 26 occur, 1.2 standard deviations.

The model was built before bases 39 to 41 were searched, so these bases are a fair test. The model expected 5.19 solutions under $0^0 = 0$ and 3.38 under $0^0 = 1$; the search found 6 and 4 #lib("5.7"). All six new solutions have $b - 1$ digits, the most likely length.

=== Predictions

#heuristic(id: "model-heur-base100", title: "Base 100", src: ("5.6", "6.6"))[
  Base 100 is even, so no parity factor applies. The model expects 1.01 nontrivial solutions per convention: 0.55 with 99 digits, 0.24 with 98, 0.09 with 97, 0.08 with 100 and 0.06 with fewer.
]

The search has excluded every base-100 solution with at most 50 digits (@sec-search-base100). The model gives such solutions a total chance of about 0.002, so this is no test. A search of base 100 itself is out of reach (@sec-search-cost).

== Testing the model by changing the weights <sec-model-tests>

A model built to fit 40 bases could fit them by accident. The strongest tests change the weights and ask whether the model follows. The engine of @ch-search accepts other weight tables (@sec-search-tree), so the same exact search runs in worlds that the model describes differently.

=== Random weights keep the count and lose the parity effect

With `--perturb`, each weight $x^x$ with $x >= 2$ gets a random extra amount of up to a quarter of its size. With `--keep-residues` the extra amount is a multiple of $2(b - 1)$, so the residues of the weights stay the same.

#computation(id: "model-comp-perturb", title: "Perturbed weights", src: "9.6")[
  Solutions with at least $b - 6$ digits in bases 16 to 28, three random seeds per base:
  #align(center, btable(columns: 3, align: (left, right, right),
    [weights], [$0^0 = 0$], [$0^0 = 1$],
    [refined model], [20.1], [14.9],
    [true weights], [16], [16],
    [random perturbation], [13.7], [13.3],
    [perturbation that keeps residues], [19.6], [14.9],
  ))
]

Random weights lose the extra solutions of odd bases under $0^0 = 0$, and the total falls to the value of the basic model. Weights that keep their residues bring the effect back, at exactly the size of the refined model. So the residues of $x^x$ cause the parity effect, and nothing else in the arithmetic of $x^x$ matters for the counts. The perturbed worlds also reproduce the emptiness law of @sec-model-empty: in 240 runs on even bases 16 to 27, 47 were empty against 44.8 predicted, and in 240 runs on odd bases, 16 against 20.6 #lib("9.7").

=== Forced residues: a factor of seventeen

The sharpest test forces the residues. The option `--set-residue r` raises each weight $w(x)$, $x >= 1$, by less than $b - 1$, so that $w(x) equiv x + r med (mod b - 1)$. Let the digit 0 weigh $z$.

#proposition(id: "model-prop-forced", title: "Forced residues", src: "17.2")[
  Suppose $w(x) equiv x + r med (mod b - 1)$ for every digit $x >= 1$ and $w(0) = z$. A $k$-digit solution with $c_0$ zeros satisfies $r(k - c_0) + z c_0 equiv 0 med (mod b - 1)$. In particular:
  #align(center, btable(columns: 4, align: (right, right, left, left),
    [$r$], [$z$], [condition on a solution], [allowed lengths],
    [0], [0], [none], [all],
    [0], [1], [$c_0 equiv 0 med (mod b - 1)$], [all, with no zero (or $b - 1$ zeros)],
    [1], [1], [$k equiv 0 med (mod b - 1)$], [only $k = b - 1$],
    [1], [0], [$k - c_0 equiv 0 med (mod b - 1)$], [$k = b - 1$ without zeros, or $k = b$ with one zero],
  ))
]
#proof[
  This is @thm-digit-sum with $w(x) - x equiv r$ for nonzero digits and $w(0) - 0 = z$.
]

With $r = 0$ and $z = 0$ the identity holds for every multiset, so the refined model predicts $b - 1$ times as many solutions as for random residues: in bases 12 to 24, about 17 times as many. With $r = 1$ and $z = 1$ only solutions with exactly $b - 1$ digits survive, and the model predicts $(b - 1)$ times the 55.2% share of that length.

#computation(id: "model-comp-forced", title: "Forced residues in bases 12 to 24", src: "17.2")[
  Bases 12 to 24, seeds 1 to 8 (104 runs per weight set, $sum (b - 1) = 1768$), solutions with at least $b - 6$ digits, against the refined model computed with the exact weights of each run:
  #align(center, btable(columns: 6, align: (left, left, right, right, right, right),
    [weights], [convention], [observed], [model], [per $b - 1$], [limit],
    [`--perturb`], [$0^0 = 0$], [98], [111.8], [], [],
    [`--perturb`], [$0^0 = 1$], [109], [111.8], [], [],
    [`--set-residue 0`], [$0^0 = 0$], [1955], [1891.4], [1.106], [1.000],
    [`--set-residue 0`], [$0^0 = 1$], [845], [789.8], [0.478], [0.368],
    [`--set-residue 1`], [$0^0 = 1$], [1030], [984.7], [0.583], [0.552],
    [`--set-residue 1`], [$0^0 = 0$], [454], [453.1], [0.257], [0.233],
  ))
]

Under $0^0 = 0$, forcing $w(x) equiv x$ multiplies the count by $1955 slash 98 = 19.9$; the model predicts $1891.4 slash 111.8 = 16.9$, and the mean of $b - 1$ is 17.0. With $w(x) equiv x + 1$ under $0^0 = 1$, all 1030 solutions have exactly $b - 1$ digits, as the identity demands. All four forced cases lie within 7% of the model. A seventeen-fold change in the count, predicted to a few percent by a model with no fitted parameter, is the best evidence that the model captures the mechanism.

Two details differ from a Poisson law, and both are structural. The counts per run scatter twice as much as Poisson counts, because forced residues fix the small weights and create families: in base 21 with `--set-residue 1`, $w(2) - w(1) = w(3) - w(2) = b$, so a digit 1, 2 or 3 in the second-to-last place gives three solutions at once. And short solutions become four times too common under `--set-residue 0`, for an algebraic reason: writing $w(x) = x + k_x (b - 1)$, a 2-digit string $(a, c)$ is a solution exactly when $a = k_a + k_c$, and $k_1 = 0$, $k_2 = 1$ for every $b >= 4$, so $(1, 2)$ and $(2, 2)$ are solutions in every base and for every seed #lib("17.2").

=== The value of $0^0$ as a free parameter

Let the digit 0 weigh $m$ under the second convention, for $m$ from $-2$ to 3. For $m$ other than 0 and 1 there are no twins and no self-paying families, so these worlds test the model without the families. @model-heur-parity predicts an odd-base factor of 2 for even $m$ and $1 + e^(-2)$ for odd $m$; at finite bases the model gives 2.00 to 2.02 and 1.19 to 1.22.

#computation(id: "model-comp-zero-m", title: [The convention $0^0 = m$], src: "17.3")[
  Bases 10 to 30, solutions with at least one zero, pooled by the parity of $m$:
  #align(center, btable(columns: 5, align: (left, left, right, right, right),
    [$m$], [bases], [observed], [model], [$P("at least observed")$],
    [even ($-2, 0, 2$)], [even], [16], [21.7], [0.91],
    [even ($-2, 0, 2$)], [odd], [42], [39.5], [0.37],
    [odd ($-1, 1, 3$)], [even], [28], [21.7], [0.11],
    [odd ($-1, 1, 3$)], [odd], [11], [10.9], [0.53],
  ))
]

The parity factor follows the parity of $m$, as predicted. Zero-free solutions are set aside in this table because they are solutions for every $m$ at once and would be counted six times. There are 24 of them in these bases, against 16.5 expected #lib("17.3").

== Near-solutions and the defect spectrum <sec-model-defects>

A base with one solution gives one data point. The defect spectrum turns each base into hundreds of data points.

#definition(id: "model-def-defect", title: "Defect spectrum", src: "11.1")[
  For a base $b$ and an integer $D$, let $N_D (b)$ be the number of integers $n$ with at least two digits and $n - F(n) = D$. The numbers counted by $N_D (b)$ with $D != 0$ are _near-solutions_ with offset $D$.
]

The search finds $N_D (b)$ exactly by starting the interval of @sec-search-tree at $D$ in place of 0. If the model is right, $D = 0$ is not special. An offset $D$ in the residue class of 0 modulo $2(b - 1)$ keeps the digit-sum identity and the parity, so it is another draw of the same coincidence, with the true weights $x^x$ and all their arithmetic. The mean of $N_D (b)$ over such offsets estimates the expected number of solutions of base $b$ without any model. Call it $lambda_m (b)$.

Short numbers need care, because $n = F(n) + D$ needs $n > D$. So the comparison counts only numbers with at least $b - 6$ digits, where every offset below $10^6$ sees the same lengths.

#computation(id: "model-comp-spectrum", title: "Solutions against their near-solutions", src: "11.1")[
  Bases 12 to 32, offsets $D = j(b - 1)$ with even $j$ up to 120, numbers with at least $b - 6$ digits:
  #align(center, btable(columns: 3, align: (left, right, right),
    [group], [solutions ($D = 0$)], [predicted by the offsets],
    [$0^0 = 0$, even bases], [13], [10.9],
    [$0^0 = 0$, odd bases], [20], [22.2],
    [$0^0 = 1$, even bases], [15], [12.8],
    [$0^0 = 1$, odd bases], [15], [14.0],
  ))
  Within a base the counts $N_D$ at single offsets have variance-to-mean ratio 0.98 (median over 42 cases). Across bases, $sum (N_0 - lambda)^2 slash lambda = 44.6$ over 42 cases with the clustered calibration of @sec-model-evidence ($P = 0.36$; 48.8 with the naive one).
]

So solutions are ordinary draws. The count at a single offset is Poisson. Across bases the number of solutions scatters around the base's own mean as a Poisson draw would. One caution, which @sec-model-evidence makes precise: the offsets are not independent of each other, so the mean $lambda$ is less precise than 60 independent offsets would make it. Odd bases under $0^0 = 0$ have twice as many near-solutions as even ones, at every offset in the class: the parity effect, now seen without the model. A base does not "know" whether it has a solution. The empty base 19 has an ordinary spectrum, with $lambda = 1.02$ under $0^0 = 1$ and 1.35 under $0^0 = 0$, inside the range 0.88 to 2.17 of the other bases.

=== How well the model predicts a single base

The ratio $lambda slash "model"$ averages 0.98 under $0^0 = 0$ and 1.12 under $0^0 = 1$ over bases 12 to 32. So the model is right on average. Its spread from base to base was first measured at about 20%, twice the sampling error of the offsets #lib("11.2a"). With the clustered variance of @sec-model-evidence about half of that excess disappears; it was an artefact of treating the offsets as independent. Part of the rest comes from the forced top digits. The top digits of $F(c)$ are fixed by the counts of the largest digits, and those top digits must also be in the multiset. The model treats them as random. A model that reads the top $t$ digits off $F$ and draws only the rest follows the bases more closely.

#computation(id: "model-comp-top", title: "Forced top digits and the scatter", src: ("23.5", "26.4"))[
  Bases 12 to 32, lengths $b - 6$ to $b$, 400,000 sampled multisets per base and length. Chi-square of $lambda slash "model"$ on 21 bases, with the naive variance of the offset means and with the clustered one:
  #align(center, btable(columns: 5, align: (right, right, right, right, right),
    [top digits forced, $t$], [$0^0 = 0$: naive], [clustered], [$0^0 = 1$: naive], [clustered],
    [0 (refined model)], [97.0], [41.4 ($P = 0.005$)], [95.7], [43.3 ($P = 0.003$)],
    [3], [68.2], [30.2 ($P = 0.09$)], [75.7], [34.7 ($P = 0.03$)],
    [4], [59.6], [28.0 ($P = 0.14$)], [72.4], [34.5 ($P = 0.03$)],
  ))
]

With the clustered variance and the top three or four digits forced, the remaining scatter under $0^0 = 0$ is noise, and under $0^0 = 1$ it is marginal. Two items remain. Under $0^0 = 1$ the model is 12% low on average in both parities, at 3.0 standard deviations; @sec-model-excess finds that this does not sit in the zeros and is about 2 standard deviations once the scatter between worlds is counted. Under $0^0 = 0$ base 19 has 0.67 times the model's rate of near-solutions; this looked like 4.6 standard errors with the naive variance and is 2.9 with the clustered one, one case among 42, so it is no longer a separate anomaly. Base 13 is high because its lengths are short and local factors of the kind in @sec-short-heuristic raise the count. @sec-model-anomalies collects the verdicts.

=== Where the 12% excess sits <sec-model-excess>

The library knows two corrections to the coincidence model: the residues
modulo $b - 1$ and the forced top digits. The 12% excess under $0^0 = 1$
could be a third one. Two exact facts help to locate it.

#lemma(id: "model-lem-zero-free", title: "Zeros and the two conventions", src: "34.1")[
  + A string without the digit 0 has the same $F$ under both conventions.
  + $F_1 (n) = F_0 (n) + z(n)$. So $n$ is a near-solution at offset $D$
    under $0^0 = 1$ with $z$ zeros exactly when it is a near-solution at
    offset $D + z$ under $0^0 = 0$ with $z$ zeros.
]
#proof[
  A zero weighs $m$, so the two sums differ by $z(n)$. And
  $n - F_1 (n) = D$ is the same as $n - F_0 (n) = D + z(n)$.
]

So the zero-free near-solutions are the same events under both
conventions, and so is their expectation in the model. The library
computes the refined model exactly, split by the number of zeros. It walks
over the digit values from $b - 1$ down, stops as soon as the length of $F$
is fixed, and handles the residue with the characters of
@sec-model-characters (Proposition 34.1 of #lib("34.1")). This replaces the
sampling of earlier chapters, and it agrees with it within the sampling
error.

#computation(id: "model-comp-zero-classes", title: "The excess by number of zeros", src: "34.1")[
  Bases 12 to 26, offsets $2 j (b - 1)$ with $j = 1, dots, 60$, numbers
  with at least $b - 6$ digits, model with the top 3 digits forced. Ratio
  of near-solutions to the model, by the number of zeros of the string:
  #align(center, btable(columns: 7, align: (left, right, right, right, right, right, right),
    [bases], [$0^0$], [zero-free], [1 zero], [2 zeros], [3 or more], [all],
    [even], [0], [0.99], [0.93], [0.80], [0.90], [0.93],
    [even], [1], [1.00], [1.30], [1.07], [0.39], [1.09],
    [odd], [0], [1.26], [1.06], [0.79], [1.01], [1.10],
    [odd], [1], [1.26], [none], [0.94], [0.64], [1.16],
  ))
  The cells 1.26 have $z = +3.4$ and the cell 1.30 has $z = +2.9$, with the
  clustered variance of @sec-model-evidence.
]

The excess is two different things. In odd bases it is a surplus of
zero-free near-solutions, the same events under both conventions. Under
$0^0 = 1$ the parity rule removes the strings with an odd number of zeros,
so 72% of the expectation is zero-free, against 42% under $0^0 = 0$. The
same surplus therefore lifts the $0^0 = 1$ ratio more, to 1.16 against
1.10. Base 13, whose lengths are short, carries almost half of it. In even
bases the zero-free class fits, and the gap between the conventions sits in
one cell, the strings with one zero under $0^0 = 1$. By the lemma these are
the near-solutions of $0^0 = 0$ at the offsets $2 j (b - 1) + 1$. A second
search at the offsets $2 j (b - 1) + 1$ and $+ 2$ shows cells of the same
size elsewhere, in other zero classes and under both conventions. So the
one-zero cell is one cell of a general scatter, not a property of the zeros.

Perturbed worlds give a control. Replace each weight $w(x)$, $x >= 2$, by
$w(x)$ plus a random amount below $w(x) slash 4$. This keeps the lengths
and destroys every residue structure. Then compare the near-solutions of
that world with the exact refined model of the same weights.

#computation(id: "model-comp-perturbed-gap", title: "The two conventions in perturbed worlds", src: "34.1")[
  Five perturbed worlds, bases 12 to 26. The gap between the pooled ratios
  under $0^0 = 1$ and $0^0 = 0$ is $-0.039$, $-0.022$, $-0.021$, $-0.032$
  and $-0.039$, with mean $-0.031 plus.minus 0.022$. With the true weights
  it is $+0.09 plus.minus 0.04$. The odd zero-free cell takes the values 0.79
  to 1.23 across the five worlds, against 1.26 for the true weights. With
  the top digits forced, one cell of the table above varies between worlds
  with a standard deviation of 0.08 to 0.09, while its clustered sampling
  error is 0.065.
]

So the clustered variance of @sec-model-evidence understates how much a
whole world can deviate from the model, by a factor of about 1.3 to 1.5 in
standard deviation. The cause of this extra variance is open (#q(139)).

#heuristic(id: "model-heur-excess", title: "No third correction", src: "34.1")[
  The 12% excess under $0^0 = 1$ is not a correction tied to the zeros.
  + In odd bases it is a surplus of zero-free near-solutions, common to
    both conventions, which weighs more under $0^0 = 1$.
  + In even bases it is one cell, and the shifted offsets show cells of
    the same size in other places.
  + Perturbed worlds show no gap between the conventions, so the model
    treats the zeros correctly. The gap of the true weights is 2.5
    standard errors above theirs, so a small effect of $x^x$ is not
    excluded.
  + With the extra variance between worlds, the $z = 3.0$ of the excess
    becomes about 2.0 to 2.3.
]

Fresh odd bases would decide whether the zero-free surplus is real
(#q(140)).

=== The zeros of the long solutions <sec-model-zeros>

The long solutions under $0^0 = 0$ seemed to have too few zero digits
(#q(71)). The exact model gives the law of the number of zeros of a
solution of given base and length, with the residue condition in place.

#computation(id: "model-comp-zeros-solutions", title: "Zero digits of the long solutions", src: "34.2")[
  Solutions with at least $b - 6$ digits in bases 12 to 43, and the zeros
  expected by the exact model:
  #align(center, btable(columns: 5, align: (right, left, right, right, right),
    [$0^0$], [bases], [solutions], [zeros], [model],
    [0], [even], [19], [10], [$16.7 plus.minus 4.0$],
    [0], [odd], [30], [19], [$26.4 plus.minus 5.0$],
    [1], [even], [21], [17], [$18.6 plus.minus 4.2$],
    [1], [odd], [25], [18], [$15.7 plus.minus 5.0$],
  ))
  Under $0^0 = 0$ that is 29 zeros against $43.1 plus.minus 6.4$, $z = -2.2$.
  Forcing the top three digits raises the expected zeros by 5% in even
  bases and lowers them by 1% in odd bases, so it does not close the gap.
]

#computation(id: "model-comp-zeros-near", title: "Zero digits of the near-solutions", src: "34.2")[
  Bases 12 to 26, the offsets of @model-comp-zero-classes. Mean number of
  zeros per near-solution, against the model:
  #align(center, btable(columns: 5, align: (right, left, right, right, right),
    [$0^0$], [bases], [observed], [model], [$z$],
    [0], [even], [0.823], [0.840], [$-0.33$],
    [0], [odd], [0.720], [0.849], [$-3.11$],
    [1], [even], [0.842], [0.842], [$-0.09$],
    [1], [odd], [0.451], [0.594], [$-2.62$],
  ))
]

The near-solutions supply thousands of digits. In even bases they have
exactly the zero rate of the model, so the even-base shortfall of the
solutions (10 against 16.7) is chance. In odd bases they are short of
zeros, but the zero classes of @model-comp-zero-classes show why: there are
too many zero-free near-solutions, not too few zeros in the others. This
is the surplus found above, seen from the other side. So the zeros do not
follow a law of their own.#footnote[Library section 24.6.2 says that the
forced top digits account for 2 to 4 of the 13.5 missing zeros. The exact
model does not support this; see #lib("34.2").]

=== Why the integer digits are almost uniform

In the function-field world of @sec-worlds-ffield the model fails, because Frobenius makes the digits of $F$ strongly structured: whole positions are always zero, and zeros are 4 to 700 times more common than the model assumes. One can ask whether the integer digits of $F$ hide a similar structure. They do not, apart from the top.

#computation(id: "model-comp-int-zeros", title: [Zero digits of $S(c)$ in the integers], src: "24.6")[
  For 100,000 random $(b - 1)$-digit strings $c$ per base with a $(b - 1)$-digit weight, in bases 11 to 41 under $0^0 = 1$: the top two or three digits of $S(c)$ are almost never zero, or zero far more often than $1 slash b$. Below them, the rate of zero digits is $1 slash b$ within 3%, at the top and at the bottom positions alike.
]

The forced top digits move the integer predictions by a few percent only: they change the chance that the zero counts of $c$ and $S(c)$ match by less than 2%, raise the parity factor under $0^0 = 1$ by 2% to 4%, and lower the total by about 1% through the $b$-digit share #lib("24.6").

There is a second lesson in the comparison. In $FF_q [T]$ the near-solution check of the library first agreed with the census, but only because adding $(B - 1) g$ to a solution there gives a near-solution with the same class sums: the offsets mapped solutions to near-solutions one to one, so they were not independent draws. The library first argued that this cannot happen in the integers, because changing digits changes $F$ by $w(d_0 - j) - w(d_0) + w(d_1 + j) - w(d_1) != 0$. That argument overlooks rearrangements. Swapping two digits keeps the multiset, so it keeps $F$, and it moves $n$ by a multiple of $b - 1$. So a multiset can be a near-solution at several offsets at once, and two thirds of the integer near-solutions share their multiset with another offset (@sec-model-evidence). The integer offsets are therefore weaker evidence than independent draws, but they are not copies of the solutions as in $FF_q [T]$, and the test of @model-comp-spectrum stands with wider error bars.#footnote[Library section 24.6.3 calls an integer near-solution "a genuine second draw". Section 26.4 corrects this.]

#remark(id: "model-rem-blocks")[
  Some solutions contain a block that pays for itself, such as $(3, 3, 6, 6, 1)$ in base 13, where $13 dot P_((3,3,6,6))(13) = 3^3 + 3^3 + 6^6 + 6^6$ (@sec-cons-blocks). In the model a solution ends in such a self-paying tail with probability $T_m (b) slash b^m$, where $T_m (b)$ counts the $m$-digit tails that pay for themselves. Under $0^0 = 1$, $T_1 (b) = 1$ (the digit 1) and $T_2 (b)$ is the number of 2-digit solutions, usually 0. So the block route is a share of about $1 slash b$ of the solutions, already counted. In bases 2 to 43 under $0^0 = 1$, 2 of the 59 solutions with at least 4 digits have an exact split at the last digit, against 3.38 expected #lib("22.5").
]

== Near-solutions as evidence <sec-model-evidence>

Almost every "chance" verdict in this document rests on near-solutions: a count at $D = 0$ is compared with its mean over many offsets in the class of 0. The library first treated the offsets as independent draws. They are not, and the reason is elementary.

#lemma(id: "model-lem-swap", title: "Swap lemma", src: "26.1")[
  Let $n$ and $n'$ have the same digit multiset in base $b$, both without a leading zero. Then $F(n') = F(n)$ and
  $ n' - F(n') = (n - F(n)) + (n' - n), quad n' - n equiv 0 med (mod b - 1). $
  If $n'$ is $n$ with the digits $x$ at position $i$ and $y$ at position $j > i$ exchanged, then $n' - n = (x - y)(b^j - b^i) = (x - y) b^i (b - 1) R_(j - i)$, where $R_s = 1 + b + dots + b^(s - 1)$. For the last two digits this is $(x - y)(b - 1)$.
]
#proof[
  $F$ depends only on the multiset. Every power of $b$ is 1 modulo $b - 1$, so a number is congruent to its digit sum, and the two digit sums agree. For the transposition only positions $i$ and $j$ change.
]

So the near-solutions of one multiset form a _cluster_: a multiset $c$ is a near-solution at every offset $D = n' - S(c)$ for which some arrangement $n'$ of $c$ puts $D$ in the offset set. A single coincidence, a weight $S(c)$ close to one of its own arrangements, is counted at several offsets. The same holds in every positional world where $F$ depends only on the multiset: negative bases, factorions, the factorial system and the Pisot base #lib("26.1").

#proposition(id: "model-prop-design", title: "What the clusters change", src: "26.1")[
  Assume that distinct multisets are independent, as the model does. Then the count $N_D$ at one offset is still Poisson, up to clumps such as twins at that offset, and the mean $lambda$ of the counts over $J$ offsets is still unbiased. But the total $T$ over the offsets has variance $phi E T$ with the _design effect_ $phi = E[K^2] slash E[K]$, where $K$ is the number of offsets at which a near-solution's multiset appears. So $J$ offsets are worth only about $J slash phi$ independent ones. Finally $N_0$ and $T$ are positively correlated, because a solution and its rearrangements lie in one cluster.
]

The design effect is the familiar quantity of cluster sampling (@app-prob): a survey that interviews whole households learns less than one that interviews the same number of unrelated people.

#computation(id: "model-comp-design", title: "Design effects", src: ("26.2", "26.3"))[
  Integer bases 12 to 26, offsets $2 j(b - 1)$, $j = 1, dots, 60$, numbers with at least $b - 6$ digits. Between 43% and 88% of the near-solutions share their multiset with another offset. The design effect is 1.5 to 3.5 (pooled 2.48 under $0^0 = 0$ and 2.14 under $0^0 = 1$), so 60 offsets are worth 26 to 29 independent ones. The partner pairs sit at the moves of @model-lem-swap: 43% at a swap of the last two digits, 20% at positions 0 and 2, 18% at positions 1 and 2. Of the 52 solutions in these bases, 29 have a rearrangement that is a near-solution in the window. A simple count of the expected partners under uniform bottom digits predicts the design effect within a few percent under $0^0 = 1$. Factorions, negative bases, near-2-cycles and the Pisot bases have design effects of 1.6 to 6.4; offset families with steps divisible by many small numbers have none.
]

A better offset family avoids the problem. Choose offsets $D = k(b - 1)$ such that no two differ by the move of a single transposition. This _transposition-free_ family cuts the shared share to about 15%, keeps the mean within 4%, and is worth about 51 of 60 offsets. For a single count $N_0$ against its offsets, the right P value mixes the Poisson law over the uncertainty of $lambda$, with the variance inflated by $phi$ and with the clumps at one offset (twins, factorion triples) built in #lib("26.3").

=== Every verdict revisited

The library recomputed every P value that rests on offsets. @tab-model-verdicts lists the main ones. The pattern is clear. Verdicts about $D = 0$ barely move, because the Poisson noise of a single count of 3 to 60 dominates the calibration error. What moves are statements about the precision of $lambda$ itself: per-base comparisons with the model and comparisons between offset families.

#tablefig(caption: [Verdicts that rest on near-solutions, with the naive and the clustered calibration #lib("26.4").], id: "tab-model-verdicts")[
  #btable(columns: 4, align: (left, right, right, left), size: 8.5pt,
    [statement], [old], [new], [verdict],
    [integers, 4 groups of @model-comp-spectrum], [$P$ 0.30 to 0.43], [0.31 to 0.43], [unchanged],
    [empty base 19, union mean 1.9], [0.15], [0.15], [unchanged],
    [no $b$-digit solution under $0^0 = 1$, 0 against 1.30], [0.27], [0.27], [unchanged],
    [per-base scatter, chi-square on 21 bases], [97, 96], [41, 43], [half an artefact],
    [base 19 near-solutions, $0^0 = 0$], [$z = -4.6$], [$z = -2.9$], [one case of 42],
    [model 12% low under $0^0 = 1$], [$z = 4.4$], [$z = 3.0$], [weaker, survives],
    [odd-base factorions, per family], [0.003 to 0.02], [0.004 to 0.025], [unchanged],
    [factorions, combined with fresh bases], [about 0.05], [about 0.09], [weaker],
    [factorions, after the choice of 16 groups], [about 0.1], [0.13], [unchanged],
    [5-digit excess, bases 13 to 99, window calibration], [0.0047], [0.0055], [unchanged],
    [the same after the choice of 10 cells], [0.015], [0.018], [unchanged],
    [negative bases, last digit kept, 42 against 52], [0.09], [0.11], [unchanged],
    [negative multiples of 3, 10 against 17.3], [0.044], [0.056], [unchanged],
    [step-$b$ offsets against step offsets, negative bases], [about 4 SD], [2.9 SD], [weaker],
    [2-cycles in even bases, 2 against 5.25], [0.10], [0.11], [unchanged],
  )
]

=== A pooled test across worlds

Each world of @ch-worlds with a near-solution calibration gives one comparison of $D = 0$ with its offsets. Pooling them tests whether $D = 0$ is special anywhere.

#computation(id: "model-comp-pooled", title: "Eight worlds pooled", src: "26.5")[
  Integers, odd-base and even-base factorions, negative bases, rational bases, the Pisot bases, Eisenstein bases and 2-cycles: 284 solutions against 297 to 304 expected from their offsets. The worlds disagree more than chance allows: the heterogeneity statistic is 17.2 to 23.3 on 7 degrees of freedom ($P = 0.002$ to 0.016), depending on the Pisot calibration. Two worlds drive it, the odd-base factorions (ratio 0.33) and the Pisot bases (ratio 1.34 to 1.56). Without them the other six fit one common ratio of 0.91, with $P = 0.60$ for heterogeneity.
]

So outside two named worlds there is no sign that $D = 0$ is special. The odd-base factorions are the shortfall found after looking at 16 groups (@sec-model-anomalies). The Pisot excess is mostly a calibration fault: for even $x$ the offsets $j x$ mix two classes modulo $2x$, and the defect spectrum peaks near $D = 0$; against a local calibration in the right class, 25 solutions against 14.8 expected has $P approx 0.05$ (@sec-worlds-pisot) #lib("26.6").

=== A ledger of P values <sec-model-ledger>

Each verdict above was judged on its own. A ledger judges them together
(@sec-app-prob-ledger). The library lists 241 statements of its chapters 3
to 32 that compare data with the model. For each one it records the test,
the P value, the data used, and whether the hypothesis was named before the
data were seen. Of the 221 statements that are still current, 133 have a P
value. Tests that share data are merged into 56 groups, each with the
smallest P value of the group after the Sidak correction.

#computation(id: "model-comp-ledger", title: "The P values of the library", src: "34.4")[
  #align(center, btable(columns: 6, align: (left, right, right, right, right, right),
    [groups], [number], [below 0.05], [expected], [median], [Fisher $P$],
    [all], [56], [14], [2.8], [0.23], [$2 dot 10^(-9)$],
    [named in advance], [12], [0], [0.6], [0.59], [0.74],
    [all others], [44], [14], [2.2], [0.18], [$3 dot 10^(-11)$],
    [without $FF_q [T]$ and the factorial system], [40], [8], [2.0], [0.24], [$2 dot 10^(-4)$],
    [integers only], [9], [3], [0.45], [0.23], [0.005],
  ))
  The 14 groups below 0.05 are the census of $FF_q [T]$ (6 groups), the
  empty bases $equiv 3 med (mod 8)$, the negative-base offsets that keep
  the last digit, the 6-digit narcissistic numbers in even bases, the
  5-digit excess, the odd-base factorions, the zeros of the long
  solutions, the $(b - 1)$-digit excess, the Pisot class and the 12% excess.
]

Every one of the 14 is already named in this document as an anomaly, a
pattern chosen after the data, or a known failure of the model.

#heuristic(id: "model-heur-ledger", title: "Selection, not a hidden flaw", src: "34.4")[
  The P values of the library are not uniform, and the cause is selection.
  + The 12 groups named in advance (fresh bases, the forced and shifted
    weights, fresh factorion bases, base 18 for 2-cycles) look like uniform
    draws: none below 0.1, Kolmogorov-Smirnov $P = 0.56$. Twelve groups
    rule out only gross flaws, such as a model that is 30% off in every
    world.
  + If each group were the smallest of $k$ looks, 14 of 56 below 0.05 would
    need $k$ about 6, and the median 0.23 would need $k$ about 3. The lower
    tail is heavier than any single $k$ gives: a few groups are real
    failures ($FF_q [T]$, the factorial system), and the rest look like
    modest selection.
  + There is no lean toward too few solutions. Among the 25 groups with
    $P < 0.2$, 17 are excesses and 8 deficits.
  + Several groups share data, for example the two conventions of one
    base. So the Fisher values overstate the evidence. The conclusion does
    not rest on them.
]

So the "chance" verdicts cannot all be closed at once by a test of
uniformity, because most tests were chosen after their data. The tests
named in advance agree with the model. More of them, written down before
fresh bases are searched, are the cheapest way to strengthen the case
(#q(104), #q(143)).

=== Are neighbouring bases independent? <sec-model-neighbours>

The model treats different bases as independent. The second
Borel-Cantelli lemma behind @conj-window needs this, and so does every
variance of a count pooled over bases. But the weights $S(c)$ are the same
numbers in every base, and only their digits change. A multiset with
largest digit $X$ is a candidate in every base above $X$.

#computation(id: "model-comp-neighbours", title: "Neighbouring bases", src: "34.5")[
  For bases 12 to 32, the residual $(lambda - "model") slash "se"$ of each
  base, with the mean of each parity removed. Correlation of neighbouring
  bases, with a P value from 20,000 permutations within each parity:
  #align(center, btable(columns: 4, align: (left, right, right, right),
    [model], [$0^0$], [lag-1 correlation], [$P$],
    [refined], [0], [$-0.31$], [0.060],
    [refined], [1], [$-0.41$], [0.067],
    [top 3 digits forced], [0], [$-0.09$], [0.65],
    [top 3 digits forced], [1], [$-0.17$], [0.46],
  ))
  The two conventions of one base correlate at $+0.85$ (refined) and
  $+0.78$ (top digits forced). No near-solution multiset of bases 12 to 26
  is a near-solution in a second base, against 0.02 expected. The forced
  top digits of one multiset in bases $b$ and $b + 1$ have correlation
  between $-0.033$ and $+0.044$.
]

The negative correlation of the refined model disappears once the top
digits are forced: it was the top-digit factor, which changes smoothly with
$b$. With 20 pairs the test excludes only correlations above about 0.4.
The strong correlation of the two conventions is @model-lem-zero-free
again: the zero-free near-solutions count under both. A pooled test must
not add the two conventions as independent counts. The library's pooled
test of @model-comp-pooled did, which makes the $z$ of its integer row too
large by a factor of about 1.3; its conclusion stands #lib("34.5").

#heuristic(id: "model-heur-independent", title: "Independence across bases", src: "34.5")[
  For the second Borel-Cantelli lemma it is enough, by a theorem of Kochen
  and Stone, that the chances of solutions in two different bases $b, b'$
  add up to at most $(1 + o(1))$ times the square of the sum of the single
  chances. In the model the only link between two bases is a multiset that
  is a candidate in both. A single multiset of $d$ digits is a solution
  with chance at most about $d! slash b^(d - 1)$, of order $b^(3 slash 2) e^(-b)$
  for $d = b$, so the link is negligible. @conj-window needs no more
  independence than the model already has, and the data show none.
]

=== Do the low digits of $F$ mix?

One can ask the model's assumption directly. Draw random strings $c$ whose weight has the right length, remove from $c$ the top three digits of $F(c)$, and ask whether the low digits of $F(c)$ have exactly the remaining copies of each value, compared with random low digits.

#computation(id: "model-comp-mixing", title: "A mixing statistic", src: "26.8")[
  The low digits of $F(c)$ agree with $c$ at the rate of random digits within 1.6% per value in the integers (base 20), in base $-20$, for factorions and in the factorial system, and within 3.7% in the Pisot base $x = 6$. $FF_5 [T]$ is the one world with a clear excess, 2.2% to 3.4% per value.
]

The statistic does not follow the model's error. It flags $FF_q [T]$ with the same sign under both conventions, where the model error changes sign, and it misses the factorial failure, which sits in the top digits. Both places where the model fails have one narrow cause, the top digits in the factorial system and the zero count in $FF_q [T]$ under $0^0 = 1$, and an average over all digit values dilutes both. The negative answer still confirms the picture of this chapter: apart from the top, the integer digits of $F$ look random.

== A Poisson limit theorem <sec-model-poisson>

The data say that the number of solutions in a base looks like a Poisson draw. In the model this can be proved, with the dependencies between solutions built in. The proof uses the Chen-Stein idea in its simplest form; @app-prob has the background.

=== The coupled model

To state a joint law for both conventions, the model must say how the events depend on each other. Split a multiset $c$ into its counts $c_0$, $c_1$ of zeros and ones and its upper part $u = (c_2, dots, c_(b-1))$. Put $V(u) = sum_(x >= 2) c_x x^x$. Then $F_m (c) = V(u) + c_1 + m c_0$.

#definition(id: "model-def-coupled", title: "Coupled model", src: "13.2")[
  For each upper part $u$, let $Y_u$ be a random integer with as many digits as $V(u)$: uniform in the basic version, and uniform on the integers of that length congruent to $V(u)$ modulo $b - 1$ in the refined version. The $Y_u$ are independent. The multiset $c$ is a model solution under convention $m$ if the digits of $Y_u + c_1 + m c_0$ form $c$.
]

The model replaces the large number $V(u)$ by a random number of the same length and, in the refined version, the same residue. It keeps the exact additions of the small digits. So three dependencies are exact: twins under $0^0 = 0$, the shared zero-free solutions, and the common residue of all completions of one upper part.

Fix a minimal length $ell >= 6$. An index $alpha$ is a multiset with $ell <= k <= b$ and at least two digits above 1, together with a convention, where the two conventions are one index when $c_0 = 0$. The condition on the upper part leaves out the self-paying families $(x, 0, dots, 0, 1)$, which have tiny mass in the model. The _cluster_ of an index is the set of indices with the same upper part. Indices in different clusters are independent.

#lemma(id: "model-lem-twins", title: "Twins are the only coupling", src: "13.2")[
  If two distinct indices in one cluster are both model solutions, then both belong to convention 0 (or are shared), and one string is the other plus 1, with last digits 0 and 1.
]
#sketch[
  The two strings are $s = Y_u + j$ and $s' = Y_u + j'$ with $|j - j'| <= b$, and they have the same upper part. A length change would force many digits $b - 1$ into one of them and change the upper part, so the lengths agree. Then compare digit sums: adding $delta > 0$ with $kappa$ carries changes the digit sum by $"ds"(delta) - kappa(b - 1)$, and $"ds"(delta) <= delta$ with equality only for $delta < b$. If both are of convention 0, the digit sum changes by exactly the change in the number of ones, which forces $delta = plus.minus 1$ and no carry: a twin pair. If one is of convention 1 with $c'_0 >= 1$ zeros, the same computation makes $c'_0$ a positive multiple of $b - 1$, so the string has at most one nonzero digit, which is excluded. Two type-1 indices have $delta = 0$.
]

#theorem(id: "thm-poisson", title: "Poisson approximation", src: "13.2")[
  Let $lambda_s$, $lambda_0$, $lambda_1$ be the expected numbers of shared, convention-0-only and convention-1-only model solutions, and let $Z_s$, $Z_0$, $Z_1$ be independent Poisson variables with these means. Then
  $ d_"TV" ((N_0, N_1), (Z_s + Z_0, Z_s + Z_1)) <= 2 b_1 + b_2, $
  where $b_1 = sum_u sigma_u^2$ is the sum over clusters of the squared expected cluster counts, and $b_2 = 2 E[T]$ with $T$ the number of model solutions under convention 0 that end in 0. For $ell = ceil(b slash 2)$ and $b >= 12$, the basic coupled model gives
  $ d_"TV" <= 14.2 slash b + 16 b^2 (b + 1) ell! slash b^ell = O(1 slash b). $
  The refined model gives the same with $14.2 kappa slash b$ in the first term and an extra factor $b - 1$ in the second term, under Assumption R below. For $12 <= b <= 6000$ the refined case holds without the assumption (@model-cor-r-small). In every base it holds without the assumption with a weaker error term, which still tends to 0 (@model-thm-anticonc).
]
#sketch[
  Compare the family of indicators $X_alpha$ with independent Poisson variables $Z_alpha$ of the same means; the counts $(N_0, N_1)$ are sums of these. Clusters are independent in both families, and total variation is subadditive over independent blocks, so it suffices to bound one cluster. Inside a cluster, compare $X$ first with independent Bernoulli variables $B_alpha$, then $B$ with $Z$. Le Cam's inequality gives $d_"TV" (B, Z) <= sum p_alpha^2 <= sigma_u^2$. For $X$ against $B$, split the probabilities by the number of ones in the outcome vector: the outcomes with at least two ones have probability at most $P(K >= 2) + sigma_u^2 slash 2$, where $K$ is the number of solutions in the cluster, and the outcomes with zero or one ones differ by at most $E[K(K - 1)] + sigma_u^2$ in total. Summing over clusters, $sum E[K(K-1)]$ is the expected number of ordered pairs of solutions in one cluster, and by @model-lem-twins these are the twin pairs, so the sum is $2 E[T]$. The error terms come from two estimates. A cluster has at most $2(b + 1)$ relevant shifts $j$, and each has probability at most $2 D! slash b^(D - 1)$ to produce the upper part, which gives $sigma_u <= 4 b (b + 1) ell! slash b^ell$. And a convention-0 solution ending in 0 has its last digit fixed, which costs a factor $1 slash b$, while the chance that the other digits fit is summable over the lengths; this gives $E[T] <= 7.1 slash b$.
]

#heuristic(id: "model-assump-r", title: "Assumption R", src: ("13.2", "29.3"))[
  There is a constant $kappa$ such that for every length $k >= b slash 2$ and every residue $r$, among uniform strings of $k - 1$ digits whose weight has $k$ digits, the share with $sum c_x (x^x - x) equiv r med (mod b - 1)$ is at most $kappa slash (b - 1)$.
]

Assumption R is about the residues of $x^x$, not about the model's randomness. It is the same assumption that gives the factor 1 for odd primes in @model-heur-parity. In odd bases the prime 2 forces $kappa >= 2$. The proof of the theorem needs it only for $k >= b slash 2$. The library first stated it for every length, and that version is false: in base 10 the only one-digit string whose weight has 2 digits is the digit 3, since $3^3 = 27$, so one residue class modulo 9 gets the whole share. For a fixed short length and a large base the same happens, because few digits are small enough.

=== Assumption R reduced to one sum <sec-model-assumption-r>

Write $m = b - 1$ and $g(x) = x^x - x$ for $x >= 1$, with $g(0) = 0$. A residue condition modulo $m$ can be written with the additive characters $e(t) = e^(2 pi i t)$. For an integer $S$,
$ 1/m sum_(h mod m) e(h (S - r) / m) = cases(1 & "if" S equiv r med (mod m), 0 & "otherwise,") $
because the sum of all $m$-th roots of unity vanishes. Take expectations: $P(S equiv r) <= (1 slash m) sum_h |E e(h S slash m)|$. When $S$ is a sum of independent digits, $E e(h S slash m)$ is a product with one factor per digit. So Assumption R follows once these factors are bounded away from 1 in modulus.

A few $h$ always give modulus 1. Every $g(x)$ is even and $g(2) = 2$, so the set $H_0$ of $h$ with $h g(x) equiv 0$ for all $x$ is ${0, m slash 2}$ for even $m$ and ${0}$ for odd $m$. These $h$ are the prime 2, the source of the parity factor. For the other $h$ and a digit range of length $L$ put
$ psi_L (h) = 1/L sum_(x < L) e(h g(x) / m), quad rho(b) = max_(ceil(b slash 2) <= L <= b, h in.not H_0) |psi_L (h)| . $

#theorem(id: "model-thm-rho", title: "Assumption R from one number", src: "29.3")[
  Let $b >= 12$ and $ell = ceil(b slash 2)$. The refined case of @thm-poisson holds without Assumption R, with
  $ kappa(b) = |H_0| + (b - 1) rho(b)^(ell - 2) . $
  So it suffices that $1 - rho(b) >= 3 ln b slash b$.
]
#sketch[
  The proof of @thm-poisson needs the residue only on the event that the weight of the top $k - 1$ digits has $k$ digits, with $k = b - j >= ell$. On that event every digit is below $L = b - theta j$ for a constant $theta >= 0.71$, because a larger digit $x$ has $x^x >= b^k$. Replace the length event by the larger event "every digit is below $L$". On it the digits are independent and uniform on ${0, dots, L - 1}$, the leading one on ${1, dots, L - 1}$. So each nonleading digit contributes the factor $psi_L (h)$, and the characters give at most $(1 slash m)(|H_0| + m rho(b)^(k - 2))$ for the share of one residue. The probabilities of the larger events still sum to at most 7.1, as in the original proof.
]

So the conditioning on the length does no harm, and Assumption R becomes a statement about one number per base.

#computation(id: "model-comp-rho", title: [The number $rho(b)$], src: "29.3")[
  For every base $b$ from 12 to 6000, every $L$ from $ceil(b slash 2)$ to $b$ and every $h$ modulo $b - 1$:
  #align(center, btable(columns: 4, align: (left, right, left, right),
    [bases], [largest $rho(b)$], [where], [$kappa(b) - |H_0|$ at most],
    [12 to 19], [0.8197], [$b = 13, 16$, $h = m slash 3$], [4.6],
    [20 to 49], [0.7954], [$b = 22$], [2.7],
    [50 to 99], [0.7807], [$b = 52$], [0.134],
    [100 to 999], [0.7725], [$b = 100$, $h = 33$], [0.00041],
    [1000 to 6000], [0.7646], [$b = 1000$, $h = 333$], [$10^(-55)$],
  ))
]

#corollary(id: "model-cor-r-small", title: "The refined Poisson theorem up to base 6000", src: "29.3")[
  For $12 <= b <= 6000$ the refined case of @thm-poisson holds unconditionally, with $kappa <= |H_0| + 5$, and with $kappa <= |H_0| + 0.0005$ for $100 <= b <= 6000$. So $kappa$ is 1 in even bases and 2 in odd bases, up to $5 dot 10^(-4)$: the factors of @model-heur-parity.
]

From base 100 on, the worst $h$ is $m slash 3$ or $m slash 6$ in every base with $3 | b - 1$, and $rho(b) <= 0.537$ in all other bases. The prime 3 is the reason.

#proposition(id: "model-prop-rho3", title: "The 3-adic limit", src: ("29.3", "15.4"))[
  If $3 | b - 1$ and $h = m slash 3$, then $psi_L (h) -> 5 slash 6 + (1 slash 6) e(2 slash 3)$ as $L -> infinity$. The limit has modulus $sqrt(7 slash 12) = 0.7638$.
]
#proof[
  Modulo 3, $g(x)$ is 2 for $x equiv 2 med (mod 6)$ and 0 otherwise. A share $1 slash 6 + O(1 slash L)$ of the $x < L$ has $x equiv 2 med (mod 6)$, and each of these contributes $e(2 slash 3)$; the others contribute 1.
]

So the computed $rho(b)$ approaches 0.7638 from above, which supports the following conjecture.

#conjecture(id: "model-conj-rho", title: [$rho(b)$ for large bases], src: "29.3")[
  $rho(b) <= 0.77$ for every $b >= 100$. For $b - 1 = p$ prime, $max_(h != 0) |sum_(x <= p) e(h (x^x - x) slash p)| = O(sqrt(p log p))$.
]

For $b - 1 = p$ prime with $1000 <= p <= 20,000$, the largest sum lies between 0.84 and 1.40 times $sqrt(p ln p)$, which is the size of the largest of $p$ sums of $p$ random unit vectors. For small prime factors of $b - 1$ there is a proof, which uses that $x^x$ modulo $p$ depends only on $x$ modulo $p (p - 1)$.

#proposition(id: "model-prop-small-p", title: "Small primes spread", src: "29.3")[
  Let $p$ be an odd prime dividing $b - 1$, let $3 p <= L <= b$ and let $p divides.not h$. Then
  $ |1/L sum_(x < L) e(h g(x) / p)| <= (3 (1 + tau(p - 1))) / sqrt(p) + (p^(3 slash 2) (1 + ln p)) / L, $
  where $tau$ counts divisors. So $g$ is close to uniform modulo every prime $p <= b^(2 slash 3 - epsilon)$ that divides $b - 1$.
]
#sketch[
  Write $x = u + k p$. Since $p equiv 1 med (mod p - 1)$, $x^x equiv u^(u + k) med (mod p)$. For fixed $u$ the sum over $k$ runs along the powers of $u$, a subgroup of $FF_p^*$. Sums of $e(a y slash p)$ over a subgroup, twisted by a character, are at most $sqrt(p)$, because they expand into Gauss sums of modulus $sqrt(p)$. Grouping the $u$ by their order gives the bound.
]

This leaves out the joint residue modulo all of $b - 1$ and the case of a prime factor $p > b^(2 slash 3)$; at most one prime factor can be that large. The literature has bounds for the number of solutions of $x^x equiv lambda med (mod p)$ @balog-broughan-shparlinski2011 @cilleruelo-garaev2016, and these bound the sums $sum_(x < p) e(a x^x slash p)$ on average over $a$. No bound below $p$ for a single $a$ seems to be known, and that is what $rho(b)$ needs. The needed statement is weaker than $o(p)$: the sum must stay below $p - 3 ln p$ for every $a$ and every initial segment of length at least $p slash 2$ (#q(112)).

=== Assumption R in the limit: anti-concentration <sec-model-anticonc>

The Poisson limit needs less than Assumption R. Let $rho^*(b)$ be the largest share of one residue class modulo $b - 1$ among the strings that the proof of @thm-poisson uses, over all lengths $k >= b slash 2$. The proof gives $b_2 <= 14.2 rho^*(b)$ in the refined model. Assumption R asks for $rho^*(b) <= kappa slash (b - 1)$, which gives the rate $O(1 slash b)$. For a limit theorem it is enough that $rho^*(b) -> 0$, at any rate. This is an _anti-concentration_ statement: a sum of independent random steps should not sit on one value with large probability. The Littlewood-Offord problem asks exactly this (@sec-app-prob-lo). The weights $x^x$ give a clean case, because the small digits have exact integer weights that grow very fast.

#lemma(id: "model-lem-dissoc", title: "Small digits are dissociated", src: "30.1")[
  Let $g(x) = x^x - x$. For every $z >= 3$, $g(z) >= 2 z g(z - 1)$. Let $2 <= z_0 <= y$ and $n <= 2 z_0 + 1$. If two multisets of $n$ digits from ${z_0, dots, y}$ have the same sum of $g$, they are equal. If moreover $n g(y) < Q$, the same holds for the sums modulo $Q$.
]
#proof[
  Since $(z slash (z - 1))^(z - 1) >= 2$, we have $z^z >= 2 z (z - 1)^(z - 1)$, and the first claim follows. For the second, suppose the multisets differ, and let $w$ be the largest digit with different counts, $c_w > c'_w$. Remove the common digits above $w$. If $w = z_0$, the sums differ by $(c_w - c'_w) g(w) != 0$. If $w > z_0$, the first sum is at least $(c'_w + 1) g(w)$, and the second is at most $c'_w g(w) + n g(w - 1)$. But $n < 2 w$, so $n g(w - 1) < g(w)$ by the first claim. Modulo $Q$, both sums lie in $[0, n g(y)]$, an interval shorter than $Q$, so congruent sums are equal.
]

So if only a few digits fall into the window ${z_0, dots, y}$, their sum tells which digits they are. A fixed multiset is unlikely, so the sum is unlikely to hit a given residue. Chernoff bounds for the number of digits in the window make this quantitative.

#theorem(id: "model-thm-lo", title: [Anti-concentration for sums of $x^x - x$], src: "30.1")[
  Let $Q >= 2$, let $y >= 3$ satisfy $(y + 3) y^y < Q$, and put $z_0 = ceil((y + 1) slash 2)$ and $J = y - z_0 + 1$. Let $X_1, dots, X_k$ be independent and uniform on ${0, dots, M}$ with $M >= y$, and let $mu = k J slash (M + 1)$ be the mean number of them in ${z_0, dots, y}$. If $J >= 11$ and $J slash 2 <= mu <= J$, then for every residue $r$
  $ P(sum_i g(X_i) equiv r med (mod Q)) <= 2 e^(-J slash 5) . $
]
#sketch[
  Let $N$ be the number of $X_i$ in the window. Condition on which indices these are and on all other values. If $N = n <= 2 z_0 + 1$, the sum over the window lies in $[0, Q)$, so at most one value of it qualifies, and by @model-lem-dissoc at most one multiset. A fixed multiset of $n$ uniform values from $J$ has probability at most $n! slash J^n$. The Chernoff bounds of @app-prob-chernoff cover $N < J slash 8$ and $N > 2 z_0 + 1$, and Stirling's formula bounds $n! slash J^n$ for $n$ in between.
]

As $Q$ grows, the largest admissible $y$ is about $ln Q slash ln ln Q$, so $J$ is about $ln Q slash (2 ln ln Q)$.

#theorem(id: "model-thm-anticonc", title: "The refined Poisson law in the limit", src: "30.1")[
  Let $b >= 12$ and $ell = ceil(b slash 2)$. In the refined coupled model,
  $ d_"TV" ((N_0, N_1), (Z_s + Z_0, Z_s + Z_1)) <= 14.2 rho^*(b) + 16 b^2 (b^2 - 1) ell! slash b^ell, $
  and $rho^*(b) <= 2 exp(-(1 slash 10 + o(1)) ln b slash ln ln b)$. So the refined coupled model has the bivariate Poisson law in the limit, without Assumption R.
]
#sketch[
  As in @model-thm-rho, replace the length event for $k$ digits by the larger event that every digit is at most $M_k$, the largest digit with $M_k^(M_k) < b^k$. On it the $k - 2$ digits after the leading one are independent and uniform on ${0, dots, M_k}$. For $k >= b slash 2$ and $b >= 12$ one checks $(M_k + 1) slash 2 <= k - 2 <= M_k + 1$, so the mean $mu$ of @model-thm-lo lies in $[J slash 2, J]$. Apply that theorem with $Q = b - 1$.
]

The rate is very slow (@model-tab-lo). The bound says nothing below $b = 10^(10)$ and little below $10^(30)$. So the two routes to Assumption R meet only in the limit. The computation of @model-comp-rho gives the strong form for bases 12 to 6000. This theorem gives a weak form for very large bases. In between only @model-conj-rho speaks.

#tablefig(caption: [The bound of @model-thm-lo, optimized over the cut-off, for $Q = 10^E$ #lib("30.1").], id: "model-tab-lo")[
  #btable(columns: 5, align: (right,) * 5,
    [$E$], [$y$], [$J$], [bound, $mu = J slash 2$], [bound, $mu = J$],
    [10], [9], [5], [0.90], [0.89],
    [30], [21], [11], [0.090], [0.036],
    [100], [56], [28], [$5.7 dot 10^(-4)$], [$8.6 dot 10^(-6)$],
    [300], [138], [69], [$9.1 dot 10^(-9)$], [$3.2 dot 10^(-13)$],
    [1000], [385], [193], [$1.1 dot 10^(-23)$], [$2.1 dot 10^(-33)$],
  )
]

The theorem never looks at $x^x$ modulo a large prime, and it works for any modulus. So it also covers a composite $b - 1$, whose joint residue @model-prop-small-p leaves open. The same proof works for the weights $x^(x + t)$ and $x!$, whose ratios $g(z) slash g(z - 1)$ also grow. For the weights $x^d$ of narcissistic numbers the residue law is exact for a simpler reason. Modulo a prime $p$, $x^d - x$ depends only on $x mod p$, and the residue factor is $p$ when $(p - 1) | (d - 1)$ and 1 otherwise. For $x^x$ the residue modulo $p$ depends also on $x mod (p - 1)$, which ties the primes of $b - 1$ together. That coupling is what makes Assumption R hard.

=== Assumption R as a collision count

The strong form of Assumption R is needed for the rate $O(1 slash b)$. Already two digits give a bound by collisions.

#proposition(id: "model-prop-collision", title: "Concentration is bounded by collisions", src: "30.2")[
  Let $X_1, dots, X_k$, $k >= 2$, be independent and uniform on ${0, dots, M}$. For every $Q >= 2$ and every residue $r$,
  $ P(sum_i g(X_i) equiv r med (mod Q)) <= N_M (Q) / (M + 1)^2, $
  where $N_M (Q)$ is the number of pairs $(x, y)$ with $0 <= x, y <= M$ and $g(x) equiv g(y) med (mod Q)$.
]
#proof[
  Condition on $X_3, dots, X_k$. Let $nu$ be the law of $g(X_1) mod Q$. The chance that $g(X_1) + g(X_2)$ hits a given class $v$ is $sum_a nu(a) nu(v - a) <= sum_a nu(a)^2$ by the Cauchy-Schwarz inequality, and $sum_a nu(a)^2 = N_M (Q) slash (M + 1)^2$.
]

So if $N_(b - 1)(b - 1) <= C b$, Assumption R holds with $kappa <= 4 C$, and a bound $b^(2 - delta)$ gives $rho^*(b) <= 4 b^(-delta)$ #lib("30.2"). For $b - 1 = p$ prime this is a question about the map $x |-> x^x - x$ modulo $p$. The map $x |-> x^x$ has a literature of its own. Balog, Broughan and Shparlinski @balog-broughan-shparlinski2011 and Cilleruelo and Garaev @cilleruelo-garaev2016 bound its collisions by $p^(23 slash 12 + o(1))$. Holden and Moree @holden-moree2006 predict their number, and Kurlberg, Luca and Shparlinski @kurlberg-luca-shparlinski2015 count its fixed points. These methods write $x^x equiv a$ as a condition on discrete logarithms. The shift by $x$ mixes addition with multiplication, so they do not transfer.

#computation(id: "model-comp-collide", title: [Collisions of $x^x$ and of $x^x - x$], src: "30.2")[
  For every prime $11 <= p < 10^5$, with $1 <= x, y <= p - 1$: the pairs with $x^x equiv y^y$ number about $2.64 (p - 1)$, within 1.2% of the Holden-Moree prediction for every $p > 50,000$. The pairs $x != y$ with $x^x - x equiv y^y - y$ number $1.002 (p - 1)$ on average for $50,000 < p < 10^5$, and between $0.981 (p - 1)$ and $1.052 (p - 1)$ for each such prime: the value for a random map. For the 426 bases $12 <= b <= 3000$ with $b - 1$ prime, @model-prop-collision bounds $(b - 1)$ times the largest share by 2.57 to 4.18.
]

#conjecture(id: "model-conj-collide", title: "Shifted collisions", src: "30.2")[
  The number of pairs $1 <= x, y <= p - 1$ with $x^x - x equiv y^y - y med (mod p)$ is $(2 + o(1))(p - 1)$ as $p -> infinity$. This gives Assumption R with $kappa <= 8 + o(1)$ for every base with $b - 1$ prime.
]

A weaker bound $p^(2 - delta)$ would already give a power rate (#q(118)). For composite $b - 1$ two digits do not mix the residues modulo small primes, and the exponential sums of @sec-model-assumption-r are the better tool. A third route would be an inverse Littlewood-Offord theorem for steps drawn from a fixed set of residues (#q(119)).

=== The correlation of the two conventions

Under the theorem, $(N_0, N_1)$ is approximately the bivariate Poisson pair $(Z_s + Z_0, Z_s + Z_1)$. Within one base its correlation is $rho(b) = lambda_s slash sqrt((lambda_s + lambda_0)(lambda_s + lambda_1))$. In the large-base limit a model solution is zero-free with probability tending to $e^(-1)$, so with the parity factors:

#heuristic(id: "model-heur-corr", title: "Shared solutions in the limit", src: "13.2")[
  #align(center, btable(columns: 7, align: (left,) + (right,) * 6,
    [], [$lambda_s$], [$lambda_0$], [$lambda_1$], [$E N_0$], [$E N_1$], [$rho$],
    [even base], [$e^(-1) = 0.368$], [0.632], [0.632], [1], [1], [0.368],
    [odd base], [$2 e^(-1) = 0.736$], [1.264], [0.399], [2], [1.135], [0.488],
  ))
]

In odd bases zero-free strings meet the parity rule of $0^0 = 1$ automatically, so they keep the factor 2, and the shared share rises. The library's correlation of 0.56 is pooled over bases 10 to 41, so it has two sources: shared solutions within a base, and the parity of the base, which lifts both means in odd bases. Drawing the 32 pairs from the bivariate Poisson laws with each base's own means, 200,000 times, gives a mean sample correlation of 0.47, with 5% to 95% range 0.19 to 0.71. A correlation of at least 0.563 has probability 0.30. So the observed 0.56 is an ordinary draw #lib("13.2").

== Empty bases <sec-model-empty>

A base is empty if it has no nontrivial solution under either convention. Bases 19, 27 and 35 are the only empty bases from 3 to 41, and base 43 has solutions.

#heuristic(id: "model-heur-empty", title: "The emptiness law", src: "9.7")[
  Let $E_0$ and $E_1$ be the expected numbers of solutions under the two conventions and $E_s$ the expected number of zero-free solutions, which count under both. If solutions occur independently, a base is empty with probability $exp(-(E_0 + E_1 - E_s))$. For bases 10 to 41 this is 14% to 18% for even bases and 4% to 9% for odd bases; at base 40, 17% and 8%.
]

The law holds in the perturbed worlds of @sec-model-tests.#footnote[The library quotes two versions of these rates. Sections 7.4 and 9.7 give 17% and 8% at base 40, with all lengths of a finite base. Section 4.5 gives 20% and 9%, the limits as $b -> infinity$ of the coupled model (@sec-model-poisson), where the short lengths no longer add solutions. The numbers in @model-heur-empty are the finite-base ones.] Odd bases are rarely empty because the parity effect doubles $E_0$. If the model is right, about one base in eight near base 40 is empty, and about one in seven in the large-base limit, so infinitely many bases are empty.

#computation(id: "model-comp-empty", title: "Empty bases in the data", src: ("9.7", "11.2"))[
  Bases 10 to 41: the model expects 2.62 empty even bases and 1.13 empty odd bases. The data have 0 and 3 (19, 27, 35). With each base's own spectrum $lambda_m (b)$ from @sec-model-defects, bases 12 to 32 expect 11.6 bases with no long solution under one convention or the other and have 11; even bases have fewer than expected, odd bases more.
]

The chance of no empty even base among 10 to 41 is 0.057 under the model, and base 44, also even, has a solution. The per-base spectra put the deficit in perspective: the total over both parities is normal, the residue modulo $b$ is the one residue the offsets do not match, and offsets $D = 2 j b(b - 1)$ that also match it predict slightly fewer solutions, not more. So no mechanism tied to $D = 0$ is visible, and the even-base deficit counts as chance.

Can one prove that infinitely many bases are empty? The library argues that the tools in this document cannot #lib("8.5"). Showing that one base is empty is a finite computation. But a congruence modulo $q$ removes only a fixed share of candidates, about $1 slash q$ of all numbers satisfy $n equiv F(n) med (mod q)$, and almost all of those are not solutions. The constructions of @ch-constructions only show that bases have solutions. And in the model each base is empty with probability about 20% (even) or 9% (odd) in the large-base limit, independently of the others; a proof would have to control these chance events in infinitely many bases at once. The opposite statement, that every large base has a solution, is equally far out of reach, and the model says it is false.

What can be said for certain is short. A base has a solution when one of the families applies: under $0^0 = 0$, every perfect power with a self-paying digit (@thm-self-paying); under both conventions, every base of a 2-digit solution (@thm-two-digit). These families cover few bases. For example, 55 bases up to $10^9$ have a 2-digit solution under $0^0 = 0$ #lib("9.7").

== Length against base <sec-model-window>

Write $J = b - k$ for a $k$-digit solution in base $b$. @thm-length gives $J >= 0$, and @heur-length-law says that $J$ is usually 1 or 2.

#computation(id: "model-comp-J", title: [The law of $J$ in the data], src: "9.9")[
  Nontrivial solutions in bases 10 to 41, by $J = b - k$:
  #align(center, btable(columns: 7, align: (left,) + (right,) * 6,
    [], [$J = 0$], [1], [2], [3], [4 to 9], [12 or more],
    [$0^0 = 0$], [2], [30], [10], [7], [8], [9],
    [$0^0 = 1$], [0], [30], [8], [6], [6], [6],
  ))
]

The solutions with a large $J$ are short: under $0^0 = 1$ they are the short coincidences of @ch-short, such as 3435 in base 10 with $J = 6$.

=== The bump beyond $ln b$

The limit law says that the expected number with $J >= j$ falls like $e^(-(j-1))$. At finite $b$, @tab-model-length-law shows values about three times the limit once $J$ passes $ln b$. The cause is the largest usable digit. A digit $x$ can appear in a $k$-digit solution only if $x^x < b^k$ (@thm-digit-bound). Now $(b - J + 1)^(b - J + 1) approx b^(b - J + 1) e^(-(J - 1))$, which drops below $b^(b - J)$ once $J > ln b + 1$. From then on a digit above $k$ becomes possible and adds solutions; after that the decay is again about $e^(-1)$ per step. So the expected number of solutions in base $b$ with $J >= j$ is $C e^(-j)$ with a bounded $C$, and with $j = ln b + a ln ln b$ it is about $C slash (b (ln b)^a)$.

=== The window

#conjecture(id: "conj-window", title: "Length window", src: "10.5")[
  Under $0^0 = 1$ and for every $epsilon > 0$:
  - only finitely many solutions with $k >= 3$ digits, apart from algebraic families such as those of @thm-binomial, lie in a base $b > k + ln k + (1 + epsilon) ln ln k$;
  - infinitely many lie in a base $b > k + ln k + (1 - epsilon) ln ln k$.
]

The reason is the pair of Borel-Cantelli lemmas (@app-prob). The expected number of solutions in base $b$ with $J > ln b + a ln ln b$ is about $C slash (b (ln b)^a)$. The sum over $b$ is finite for $a > 1$, so by the first lemma only finitely many bases have such a solution. It is infinite for $a <= 1$, and in the model the bases are independent, so by the second lemma infinitely many do. That independence is an assumption of the model. @sec-model-neighbours tests it and finds no dependence between neighbouring bases. This is the same law as for the longest run of heads in $n$ coin flips, which is $log_2 n + O(log log n)$.

The library first stated a cruder window, $b <= k + (1 + epsilon) ln k$, and drew from it that each length has only finitely many solutions under $0^0 = 1$. The binomial families of @thm-every-length-m1 refute that: they give infinitely many solutions of every length $k >= 3$, in bases far above $k$, for an algebraic reason the model cannot see. Hence the exception for algebraic families in the conjecture.

#computation(id: "model-comp-window", title: "Exceptions to the window", src: "10.5")[
  Solutions under $0^0 = 1$ with $k >= 3$ and $J > ln b + 2$:
  #align(center, btable(columns: 4, align: (left, left, right, right),
    [region], [digits], [expected (model)], [observed],
    [bases 10 to 41 and 43, every length], [3 to 5], [0.96], [5],
    [], [6 to 10], [0.86], [0],
    [], [11 or more], [1.21], [2],
    [bases 44 to 127, up to 30 digits], [3 to 5], [0.05], [2],
    [], [11 or more], [0.00], [1],
    [bases 128 to 5000], [3 to 5], [0.01], [2],
  ))
]

The long exceptions agree with the model: 3 observed against about 1.2 expected, and one of the three lies in base 64, which has self-paying digits. The short exceptions do not: 9 against 1.0. That is expected, because the per-base model is the wrong tool for short strings. For a short string the base is the root of a polynomial (@thm-one-base), and the right question is whether that root is an integer. @sec-short-heuristic develops that heuristic. It explains the short solutions in the searched ranges, but it too misses the algebraic families.

For a fixed large length $k$, the model puts a $k$-digit solution in base $k$ with probability 8%, $k + 1$ with 55%, $k + 2$ with 23%, and so on. The expected number of bases with a $k$-digit solution is about 1, so a length has no base with probability about $e^(-1) = 37%$ and two or more with probability about 26%. Under $0^0 = 1$, 7 of the 29 lengths from 2 to 30 have no solution in any base up to 127, which is 24% #lib("3.4"). The missing lengths are missing only near the length: the binomial families supply every length in astronomically large bases.

== Cycles of $n |-> F(n)$ <sec-model-cycles>

Solutions are the fixed points of $n |-> F(n)$. The other cycles of this map are a natural second test, because a random mapping has a known number of cycles of each length.

#proposition(id: "model-prop-cycles", title: "Cycles live on multisets", src: "15.1")[
  Let $cal(M)_b$ be the set of digit multisets with 1 to $b$ digits and at least one nonzero digit. The map $c |-> (text("multiset of") S(c))$ sends $cal(M)_b$ into itself, and its cycles correspond one to one to the cycles of $n |-> F(n)$ on the integers $n >= 1$.
]
#proof[
  A multiset with at most $b$ digits has $S(c) <= b(b - 1)^(b-1) < b^b$, so $S(c)$ has at most $b$ digits, and it has a nonzero digit because $S(c) >= 1$. $F$ depends only on the multiset, so a cycle of integers gives a cycle of multisets of the same length. Two members of an integer cycle with the same multiset have the same image, and a cycle is a bijection on its members, so they are equal. Conversely, a multiset cycle gives the cycle of the integers $S(c)$.
]

$|cal(M)_b| = binom(2b, b) - b - 1$,#footnote[The multisets with at most $b$ digits over the values $0, dots, b - 1$ number $binom(2b, b)$, counting the empty one. Removing the empty multiset and the $b$ multisets made of zeros only leaves $binom(2b, b) - b - 1$.] so a full census is a walk over about $4^b slash sqrt(pi b)$ points. The engine walks each multiset once, with 2 bits of state per multiset; base 17 takes 670 seconds per convention, and base 18 about an hour #lib("15.1", "23.3").

The parity invariant of @thm-parity-invariant splits the map in odd bases under $0^0 = 0$: even numbers map to even numbers and odd ones to odd ones. A map from a finite nonempty set to itself has a cycle, so every odd base has a cycle of even numbers, and so a cycle besides the fixed point 1 #lib("15.1").

=== A random mapping with the invariant

A uniform random mapping on $N$ points has about Poisson$(1 slash L)$ cycles of length $L$ #cite(<flajolet-odlyzko1990>). The map $F$ is not uniform: the length of $S(c)$ and its residue modulo $b - 1$ are fixed by $c$. The class-lumped model keeps exactly this information. A class is a pair $K = (k, r)$: the $k$-digit multisets with digit sum $r$ modulo $b - 1$. In the model the image of $c$ is a random multiset of the class of $S(c)$, weighted by the number of strings with that multiset. Let $M$ be the matrix of class transitions.

#proposition(id: "model-prop-cycle-model", title: "Expected cycle counts", src: "15.1")[
  In the class-lumped model the expected number of cycles of length $L$ is $(1 slash L)$ times the sum, over $L$-tuples of distinct multisets, of the product of their transition probabilities. Up to the terms with a repeated multiset this is $(1 slash L) "tr"(M^L)$.
]

The spectrum of $M$ explains the parity effect for cycles. In odd bases under $0^0 = 0$, $M$ splits into an even and an odd block, the eigenvalue 1 has multiplicity 2, and $E_L approx 2 slash L$. Under $0^0 = 1$ the parity flips with the parity of the number of zeros; $E[(-1)^z] = (1 - 2 slash b)^k approx e^(-2)$, so $M$ has the eigenvalues 1 and about $e^(-2)$, and $E_L approx (1 + e^(-2 L)) slash L$. For $L = 1$ this is the factor $1 + e^(-2)$ of @model-heur-parity, seen from a new side.

#computation(id: "model-comp-cycles", title: "Cycles in bases 3 to 18", src: ("15.1", "23.3"))[
  Cycles of length 2 in bases 4 to 18 against the class-lumped model:
  #align(center, btable(columns: 5, align: (left, right, right, right, right),
    [group], [2-cycles], [model $E_2$], [$P(X <= "obs")$], [near-2-cycles per offset],
    [even, $0^0 = 0$], [2], [4.02], [0.24], [5.25],
    [even, $0^0 = 1$], [4], [4.30], [0.57], [4.97],
    [odd, $0^0 = 0$], [6], [7.23], [0.42], [8.32],
    [odd, $0^0 = 1$], [4], [3.88], [0.65], [3.92],
  ))
  The total number of cycles of all lengths in bases 3 to 17 matches the model in all four groups (for example 92 against 94.4 in odd bases under $0^0 = 0$). Fixed points are in excess by a factor 1.4 to 1.8, because of the constructions and the small bases.
]

=== The image of $F$

A random mapping also predicts how many points are hit. The image of $F$ is much smaller than that prediction.

#proposition(id: "model-prop-image", title: "Coincident sums", src: "26.7")[
  The image of the multiset map is the same under both conventions. Under $0^0 = 0$, multisets that differ only in their zeros have the same weight; under $0^0 = 1$, multisets that differ only in the split of $c_0 + c_1$ have the same weight.
]
#proof[
  Under $0^0 = 0$ a zero weighs nothing, and under $0^0 = 1$ zeros and ones both weigh 1. So under both conventions the image is the set of multisets of $S_0 (e)$ for the zero-free multisets $e$ of 1 to $b$ digits.
]

#computation(id: "model-comp-image", title: "The image share", src: "26.7")[
  The share of multisets with at least one preimage is 0.21 in base 10 and falls to 0.14 in base 16. The class-weighted random mapping predicts 0.38 to 0.31. Counting the distinct weights, not the multisets, closes 55% to 66% of the gap, and keeping the true top three digits of each weight closes about two thirds of the rest. The in-degrees are overdispersed: variance-to-mean 3.6 to 6.3 against 2.3 to 3.8 in the model.
]

So the forced top digits show up once more: the weights $S(c)$ share their leading digits far more than random integers do, and their multisets collide. The cycle counts above are not affected much, because they depend on the trace of the class matrix, not on the image.

An early observation said that every odd base from 3 to 11 has a 2-cycle under $0^0 = 0$ and no even base from 4 to 10 does. That is the parity doubling of the invariant plus chance: bases 13 and 15 have no 2-cycle, base 16 has one, base 18 has one. The deficit in even bases was tested with near-2-cycles, $F(F(n)) = n - j(b - 1)$, which keep every residue the map preserves. They come at the normal rate, 5.25 per offset against 4.02 in the model, so there is no second invariant #lib("23.3").

== Anomalies and how they were resolved <sec-model-anomalies>

A model tested on many groups of data will show a few deviations by chance. The library found several, and each one taught something. Before going through them, one statistical point.

#remark(id: "model-rem-look-elsewhere", title: "The look-elsewhere effect")[
  A deviation found by looking at the data is weaker evidence than its P value suggests. If you split the data into 14 groups and pick the most extreme one, a P value of 0.02 for that group is not surprising: the chance that at least one of 14 independent groups reaches 0.02 is $1 - 0.98^14 approx 0.25$. So the library corrects each P value for the number of groups it looked at, and it values fresh data, collected after a pattern was noticed, far above old data. A pattern that weakens in fresh data was probably chance.
]

/ The $(b-1)$-digit excess: In bases 10 to 38 under $0^0 = 1$, solutions with $b - 1$ digits were 1.6 times as common as the refined model predicts: 27 against 17.3, with $P = 0.019$ #lib("5.5"). But this was the most extreme of about 14 groups, so the corrected chance was about 23%. Correlation tests found nothing: the top 10 digits and the bottom 8 digits of $S(c)$ fit the multiset no more often than random digits do. In fresh bases 39 to 43 the excess continued weakly (5 against 2.45, $P = 0.10$). The resolution came from the perturbed weights of @sec-model-tests: over all lengths from $b - 6$ to $b$, the true counts fit the model, 16 against 14.9 in bases 16 to 28 and 17 against 14.6 in bases 29 to 41 #lib("9.6"). The excess at $b - 1$ digits is a fluctuation in how the solutions spread over the lengths; their total is normal.

/ Empty bases $equiv 3 (mod 8)$: Bases 19, 27 and 35 are all $equiv 3 med (mod 8)$, and so is 11, which has solutions. Three empty bases among the four such bases from 11 to 35 has probability about $10^(-3)$ in the model. But the residue class was noticed after the data, and among all 15 odd bases from 11 to 39 three empty ones has probability about 6%. Base 43, the next base $equiv 3 med (mod 8)$, has a solution #lib("4.5", "8.5").

/ Missing $b$-digit solutions: No base from 3 to 45 has a $b$-digit solution under $0^0 = 1$, against 3.6 expected in the refined model. This was the original conjecture of the library: no $b$-digit solutions at all. Under $0^0 = 0$ it is false, with bases 15 and 16. The defect spectrum showed that the model overestimates this length. Restricted to exactly $b$ digits, the offsets in bases 10 to 30 predict 1.30 solutions under each convention, against 2.33 and 1.74 from the model #lib("11.2"). The cause is the forced top digits. A $b$-digit sum needs at least three copies of $b - 1$, its leading digit is then 1 and the next one is about $0.10 b$, and these digits must also lie in the multiset, whose counts are depressed by the three copies of $b - 1$. The exact correction for the top one to three digits is 0.6 to 0.91 in bases 16 to 30, and it shrinks like $1 slash b$. With the spectrum's calibration, no $b$-digit solution under $0^0 = 1$ in bases 10 to 30 has probability 0.27. So the model still predicts a $b$-digit solution under $0^0 = 1$ in about 8% of large bases, and the search has simply not reached one.

/ The even-base empty deficit: No even base from 10 to 41 is empty, against 2.62 expected ($P = 0.057$). @sec-model-empty explains why it counts as chance.

/ Factorions in odd bases: With the weights $x!$, long factorions are rare in odd bases: 3 and 4 against about 11.9 per convention in bases 14 to 36. Offsets that keep every residue up to $b + 1$ and modulo $b^3$ give normal near-factorion counts, so no congruence explains it. Fresh odd bases 37 to 47 give 3 per convention against 6.2. With the clustered calibration of @sec-model-evidence the combined evidence has $P approx 0.09$, and 0.13 after the choice among 16 groups. The library counts it as an unexplained fluctuation (@sec-worlds-weights).

/ Base 19: The empty base 19 also has few near-solutions under $0^0 = 0$, 0.67 times the model's rate. With the naive variance this was 4.6 standard errors, a real anomaly. With the clustered variance it is 2.9, one case among 42 bases, and no longer a separate anomaly #lib("26.4").

Some deviations remain open. Each is a question in @sec-open-list.

- Under $0^0 = 1$ the per-base rate of near-solutions is 12% above the refined model, in odd and even bases alike. It survives the clustered calibration at 3.0 standard deviations #q(70). It is a zero-free surplus in odd bases and one cell in even bases, and perturbed worlds scatter enough to bring it to about 2 standard deviations (@model-heur-excess).
- Base 19 is low in its near-solutions, now 2.9 standard errors #q(68). The question has lost most of its basis.
- The long solutions under $0^0 = 0$ in bases 12 to 43 contain fewer zero digits than the model predicts: 29 against 43.1, about 2.2 standard deviations #q(71). The forced top digits do not explain this. The near-solutions show no deficit in even bases, and in odd bases their deficit is the zero-free surplus (@sec-model-zeros). So the parallel with the function-field world (@sec-worlds-ffield) is weak.
- The model's per-base predictions seemed to scatter about 20% beyond sampling error. With the clustered variance and the top digits forced, the scatter is noise under $0^0 = 0$ and marginal under $0^0 = 1$ ($P = 0.03$) #q(44).
- In even Pisot bases, offsets $j x$ with even $j$ carry 1.5 to 2.4 times as many near-solutions as those with odd $j$ under $0^0 = 0$. The identity behind this class factor modulo $2x$ is unknown #lib("26.6").
