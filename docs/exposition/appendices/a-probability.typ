#import "../template.typ": *

= Probability: Poisson approximation, Borel-Cantelli and entropy <app-prob>

The probabilistic model of @ch-model treats a Munchausen number as a rare coincidence. Rare coincidences are counted with the Poisson law. This appendix collects the facts from probability that the main text uses: the Poisson limit and how good it is, the two Borel-Cantelli lemmas, the digit counts of a random number, the statistics that compare counts with a model, and the entropy argument behind the search bound of @sec-search-entropy. A good general reference is Durrett's textbook @durrett2019. For Poisson approximation the standard book is @barbour1992, and for entropy @cover-thomas2006.

== Rare events and the Poisson law <sec-app-prob-poisson>

#definition(id: "app-prob-def-poisson", title: "Poisson law")[
  A random variable $Z$ with values in ${0, 1, 2, dots}$ is Poisson with mean $lambda >= 0$ if $P(Z = k) = e^(-lambda) lambda^k slash k!$. Its mean and its variance are both $lambda$. In particular $P(Z = 0) = e^(-lambda)$.
]

The Poisson law appears whenever many unlikely and nearly independent events are counted. Let $X_1, dots, X_N$ be indicators with $P(X_i = 1) = p_i$, and let $W = X_1 + dots + X_N$ and $lambda = p_1 + dots + p_N$. If every $p_i$ is small and the $X_i$ are independent, then $W$ is close to Poisson with mean $lambda$. To say how close, we need a distance between laws.

#definition(id: "app-prob-def-tv", title: "Total variation distance")[
  For two probability laws $P$ and $Q$ on the same countable set, the total variation distance is
  $ d_"TV" (P, Q) = sup_A |P(A) - Q(A)| = 1/2 sum_x |P(x) - Q(x)|, $
  the supremum over all events $A$. For random variables we write $d_"TV" (W, Z)$ for the distance between their laws.
]

So $d_"TV" (W, Z) <= epsilon$ means that every statement about $W$, such as "$W = 0$" or "$W >= 3$", has the same probability for $Z$ up to $epsilon$. Two facts make the distance easy to use. It does not grow when one applies a function: $d_"TV" (f(W), f(Z)) <= d_"TV" (W, Z)$. And for vectors with independent components it is subadditive: the distance between $(W_1, W_2)$ and $(Z_1, Z_2)$ is at most $d_"TV" (W_1, Z_1) + d_"TV" (W_2, Z_2)$.

#theorem(id: "app-prob-lecam", title: "Le Cam's inequality", status: "cited")[
  Let $X_1, dots, X_N$ be independent indicators with means $p_i$, $W = sum X_i$ and $lambda = sum p_i$. Then
  $ d_"TV" (W, "Poisson"(lambda)) <= sum_i p_i^2 . $
]

The proof (@lecam1960) couples each $X_i$ with a Poisson variable of mean $p_i$ that differs from it with probability at most $p_i^2$. For Munchausen numbers in one base, the indicators are "this digit multiset is a solution", there are about $4^b$ of them, and each has a tiny probability. So the squared sum is negligible, if the events are independent. They are not quite: twins under $0^0 = 0$ (@thm-twins) come in pairs, and a zero-free solution counts under both conventions (@thm-conventions). The Chen-Stein method handles such dependence.

== The Chen-Stein method <sec-app-prob-chen-stein>

Chen @chen1975 adapted Stein's method for the normal law to the Poisson law. The form below is due to Arratia, Goldstein and Gordon @arratia1989. Give each index $alpha$ a neighbourhood $B_alpha$ that contains $alpha$: the indices whose events may depend strongly on $X_alpha$.

#theorem(id: "app-prob-agg", title: "Chen-Stein bound", status: "cited")[
  Let $W = sum_alpha X_alpha$ be a sum of indicators with $p_alpha = E X_alpha$ and $lambda = sum p_alpha$. Put
  $ b_1 = sum_alpha sum_(beta in B_alpha) p_alpha p_beta, quad b_2 = sum_alpha sum_(beta in B_alpha, beta != alpha) E[X_alpha X_beta], $
  $ b_3 = sum_alpha E abs(E[X_alpha - p_alpha | X_beta : beta in.not B_alpha]). $
  Then $d_"TV" (W, "Poisson"(lambda)) <= b_1 + b_2 + b_3$.
]

The three terms have a plain meaning. $b_1$ is small when every neighbourhood has a small total probability. $b_2$ is small when two events in one neighbourhood rarely happen together. $b_3$ measures how much $X_alpha$ depends on the events outside its neighbourhood; if $X_alpha$ is independent of them, $b_3 = 0$. The theorem has sharper constants, $(1 - e^(-lambda)) slash lambda$ in front of $b_1 + b_2$, which matter when $lambda$ is large.

#example(title: "How the Poisson theorem of chapter 3 uses it")[
  The coupled model of @sec-model-poisson replaces the large-digit part $V(u)$ of the sum of a multiset by a random number $Y_u$, one for each upper part $u$. All multisets with the same upper part form a cluster, and different clusters are independent. So $b_3 = 0$ when the neighbourhoods are the clusters. The library proves that inside a cluster two events can both happen only as a twin pair (Lemma 13.7 of #lib("13.2")). So $b_2$ is twice the expected number of twin pairs, which is $O(1 slash b)$, and $b_1$ is a sum of squared cluster masses, which decays faster than any power of $b$. The library proves a cluster version directly, without the general theorem: it compares the indicator vector of each cluster with independent Bernoulli variables, and then uses Le Cam's inequality. The result is @thm-poisson: the pair $(N_0, N_1)$ of counts under the two conventions is within $O(1 slash b)$ of a bivariate Poisson law.
]

A bivariate Poisson pair has the form $(Z_s + Z_0, Z_s + Z_1)$ with independent Poisson variables $Z_s, Z_0, Z_1$. The shared part $Z_s$ counts the zero-free solutions. Its correlation is $lambda_s slash sqrt((lambda_s + lambda_0)(lambda_s + lambda_1))$, which is how the model predicts the correlation of $N_0$ and $N_1$ across bases (#lib("13.2")).

== Chebyshev and the Borel-Cantelli lemmas <sec-app-prob-bc>

#theorem(id: "app-prob-chebyshev", title: "Chebyshev's inequality", status: "cited")[
  For a random variable $Y$ with mean $mu$ and variance $sigma^2$, and every $t > 0$, $P(|Y - mu| >= t) <= sigma^2 slash t^2$.
]

The two Borel-Cantelli lemmas decide whether infinitely many of a sequence of events $A_1, A_2, dots$ happen.

#theorem(id: "app-prob-bc", title: "Borel-Cantelli lemmas", status: "cited")[
  + If $sum_n P(A_n) < infinity$, then with probability 1 only finitely many $A_n$ happen.
  + If the $A_n$ are independent and $sum_n P(A_n) = infinity$, then with probability 1 infinitely many $A_n$ happen.
]

#proof[
  (1) The number of events that happen has finite expectation $sum P(A_n)$, so it is finite with probability 1. (2) The chance that none of $A_n, dots, A_N$ happens is $product (1 - P(A_i)) <= exp(-sum_(i=n)^N P(A_i))$, which tends to 0 as $N -> infinity$. So after every $n$ some event happens.
]

The model of @ch-model treats the bases as independent trials. A statement such as "only finitely many solutions lie far from their length" then follows from the first lemma, and its converse from the second. This is how the library derives the length window, @conj-window (#lib("9.9", "10.5")). The heuristic step is the model itself. The lemmas are exact.

#example(title: "The longest run of heads")[
  Flip a fair coin forever, and let $A_n$ be the event that a run of at least $r_n$ heads starts at flip $n$. Then $P(A_n) = 2^(-r_n)$. Take $r_n = log_2 n + a log_2 log_2 n$. Then $P(A_n) = 1 slash (n (log_2 n)^a)$, and $sum_n P(A_n)$ is finite exactly when $a > 1$. The events are not independent, but they are nearly so for far apart $n$, and the conclusion holds: runs longer than $log_2 n + (1 + epsilon) log_2 log_2 n$ occur only finitely often, while runs longer than $log_2 n + (1 - epsilon) log_2 log_2 n$ occur infinitely often. In base $b$, the model gives a solution with $J = b - k > ln b + a ln ln b$ digits missing a probability of about $C slash (b (ln b)^a)$, the same sum. So @conj-window has the same shape as the law of the longest run.
]

== Digit counts of a random number <sec-app-prob-digits>

Draw a $d$-digit string uniformly in base $b$. The number of copies of one fixed digit value is binomial with $d$ trials and success probability $1 slash b$, so its mean is $d slash b$. If $b$ grows and $d = b - j$ for a fixed $j$, the mean tends to 1, and the binomial law tends to the Poisson law with mean 1 (by Le Cam's inequality, the error is at most $d slash b^2$). The counts of finitely many fixed values, such as $b - 1, b - 2, b - 3$, become independent Poisson variables in the limit.

This is the whole content of @heur-length-law. A digit $b - y$ weighs $(b - y)^(b - y) approx e^(-y) b^(b - y)$, so the sum $F$ is decided by the largest digit present and its number $c$ of copies. With $c$ copies of $b - 1$ the sum is about $(c slash e) b^(b - 1)$:

#align(center, btable(
  columns: 3,
  align: (left, left, right),
  [length of $F$], [event], [limit probability],
  [$b$], [$c >= 3$ copies of $b - 1$], [$1 - (5 slash 2) e^(-1) = 0.080$],
  [$b - 1$], [$c = 1$ or $2$], [$(3 slash 2) e^(-1) = 0.552$],
  [$b - 2$], [no $b - 1$, some $b - 2$], [$e^(-1)(1 - e^(-1)) = 0.233$],
  [$b - 3$], [largest digit $b - 3$], [$e^(-2)(1 - e^(-1)) = 0.086$],
))

The probabilities add to 1, because the events cover almost every string. That is why the model expects about one solution per base and convention, before the parity effect of @sec-model-refined. The same computation with other weights gives other length laws (@sec-worlds-weights).

== Comparing counts with a model <sec-app-prob-stats>

The library tests the model with simple statistics. Three of them recur.

- Poisson tail probabilities. If a model predicts a mean $mu$ and the data show $k$, the library reports $P(X >= k)$ or $P(X <= k)$ for a Poisson variable $X$ with mean $mu$. For example 3 observed against 0.33 expected gives $P(X >= 3) = 0.0047$ (#lib("22.4")).
- The dispersion statistic. For counts $N_1, dots, N_r$ with predicted means $lambda_1, dots, lambda_r$, the sum $sum_i (N_i - lambda_i)^2 slash lambda_i$ is about $r$ when every count is Poisson. A much larger value shows extra scatter, for example from families of solutions that come in groups (#lib("17.2")). This is Pearson's chi-square statistic.
- The look-elsewhere effect. If one picks the most extreme of $N$ groups after looking at the data, a tail probability $p$ for that group is worth about $1 - (1 - p)^N approx N p$. The library uses this to discount several striking patterns. For example a deviation with $p = 0.019$, chosen among about 14 groups, has a chance of about 23% to appear somewhere (#lib("5.5")).

Many apparent anomalies of the data turned out to be chance after one of these corrections, or after fresh data. @sec-model-anomalies tells these stories.

== Clustered samples and the design effect <sec-app-prob-design>

The near-solution test of @sec-model-defects estimates the expected number of solutions of a base by the mean count of near-solutions $n = F(n) + D$ over $J$ offsets $D$. If the offset counts were independent Poisson draws, that mean would have variance $lambda slash J$. They are not independent. A rearrangement of the digits of $n$ keeps $F(n)$ and moves $n$ by a multiple of $b - 1$, so one multiset whose sum lies close to its own arrangements is a near-solution at several offsets at once (Lemma 26.1 of #lib("26.1")). The counts come in clusters. Survey statistics has a standard language for this.

#definition(id: "app-prob-def-icc", title: "Intraclass correlation and design effect")[
  Suppose that $n$ observations fall into clusters of $m$ each, all with variance $sigma^2$, and that two observations in one cluster have correlation $rho$ while observations in different clusters are independent. The number $rho$ is the intraclass correlation. The mean of all $n m$ observations has variance
  $ sigma^2 / (n m) (1 + (m - 1) rho) . $
  The factor $"deff" = 1 + (m - 1) rho$ is the design effect, and $n m slash "deff"$ is the effective sample size: the number of independent observations that would give the same precision.
]

With $rho = 0$ nothing changes. With $rho = 1$ every cluster repeats one value, the design effect is $m$, and only the $n$ clusters count. Ignoring a positive $rho$ makes an estimate look more precise than it is.

For rare events the clusters have random sizes, and a cleaner form applies. Write the total over the offsets as $T = sum_c K_c$, where $K_c$ is the number of offsets at which the multiset $c$ is a near-solution. Different multisets are independent in the model, and each one is a near-solution only rarely, so
$ "Var" T approx sum_c E[K_c^2] = phi E[T], quad phi = E[K^2] / E[K], $
with the moments taken over the multisets that appear at least once. The design effect $phi$ is the mean cluster size seen from a random near-solution. A Poisson variance, $E[T]$, understates the scatter of $T$ by the factor $phi$, and the mean over $J$ offsets is worth only $J_"eff" = J slash phi$ independent offsets. If several near-solutions can also clump at one offset, such as twins under $0^0 = 0$ (@thm-twins), each single count has variance $psi lambda$ with $psi = E["clump"^2] slash E["clump"]$, a compound Poisson law, and $J_"eff" = J psi slash phi$ (Proposition 26.5 of #lib("26.1")).

#example(title: "The integer offsets")[
  In bases 12 to 26, with the 60 offsets $D = 2 j (b - 1)$, about two thirds of the near-solutions share their multiset with another offset. The design effect is 2.1 to 2.5, so the 60 offsets are worth about 27 independent ones (#lib("26.2")). A swap of the last two digits explains the largest share of the partner pairs, and a simple count of partners predicts $phi$ within a few percent. Offsets chosen so that no two differ by a single transposition cut the shared share to about 15% and nearly double $J_"eff"$, with the same mean.
]

How the P values change depends on the question. A single offset count is still Poisson, because each multiset is a near-solution at a given offset at most once. So when one compares the count $N_0$ of true solutions with the offset mean $hat(lambda)$, the variance of the difference is $psi lambda + phi lambda slash J$, and the first term dominates for $J >= 20$. Most "chance" verdicts of the library therefore stand (Table 4.1 of #lib("26.4")). Comparisons of the offset means themselves change a lot, because there the second term is everything. The chi-square of $lambda slash "model"$ over 21 bases falls from about 97 to about 42 once the clustered variance is used, and the low near-solution rate of base 19 goes from 4.6 to 2.9 standard errors. The library also uses a rank P value, $(1 + \#{D : N_D <= N_0}) slash (J + 1)$, which is exact when the counts at $D = 0$ and at the offsets are exchangeable, whatever the clusters, but cannot go below $1 slash (J + 1)$ (#lib("26.3")).

Two tools combine evidence across groups.

- Fisher's method. If $p_1, dots, p_k$ are independent P values, then under the null hypothesis $-2 sum_i ln p_i$ has the chi-square law with $2k$ degrees of freedom. The library uses it to combine an in-sample P value, after the look-elsewhere correction, with the P value of fresh bases; for the factorion shortfall the combined value moved from about 0.05 to about 0.09 with the clustered calibration (#lib("23.1", "26.4")).
- Pooled ratios and heterogeneity. Each group $i$ gives an observed count $O_i$ and an offset estimate $E_i$, with a variance $v_i$ that includes the design effect. A common ratio $theta = O slash E$ is estimated by weighting each group by $1 slash v_i$. Cochran's statistic $Q = sum_i (O_i - hat(theta) E_i)^2 slash v_i$ has about the chi-square law with $k - 1$ degrees of freedom if all groups share one ratio. Over eight number systems the library finds $Q = 23.3$ on 7 degrees of freedom (P about 0.002). Without the odd-base factorions and the Pisot bases, the other six worlds fit one ratio, 0.91, with $Q = 3.6$ on 5 degrees of freedom (P = 0.60) (#lib("26.5")). So outside two named worlds the solutions behave like their near-solutions, which is the claim of @ch-model.

== Entropy and the asymptotic equipartition property <sec-app-prob-entropy>

#definition(id: "app-prob-def-entropy", title: "Entropy and varentropy")[
  Let $X$ take values in a countable set with probabilities $P(x)$. The entropy of $X$ is $H = E[-ln P(X)] = -sum_x P(x) ln P(x)$, measured in nats. The varentropy is $V = "Var"(-ln P(X))$, the variance of the same quantity.
]

Entropy measures how many values a random variable really takes. A uniform variable on $M$ values has $H = ln M$. For a vector of independent components, entropies and varentropies add. The key fact is that a long vector of independent components almost always takes a value with probability close to $e^(-H)$.

#theorem(id: "app-prob-aep", title: "Asymptotic equipartition property", status: "cited")[
  Let $X_1, X_2, dots$ be independent and identically distributed with entropy $H$. Then $-1/n ln P(X_1, dots, X_n) -> H$ in probability. So for large $n$ the vector lies, with probability close to 1, in a typical set of about $e^(n H)$ values, each with probability about $e^(-n H)$. Every set that holds the vector with probability at least $p > 0$ has at least about $p e^(n H)$ elements.
]

See @cover-thomas2006[chapter 3]. The last sentence is the useful one for searching. If a search must find a hidden object that is drawn from a law with entropy $H$, and the search tries candidates one by one, it must try about $e^H$ of them to succeed with a fixed probability. A one-shot version needs only Chebyshev's inequality.

#proposition(id: "app-prob-one-shot", title: "A one-shot entropy bound", src: "10.2")[
  Let $X$ have entropy $H$ and varentropy $V$. If a set $S$ contains $X$ with probability $p$, then $|S| >= (p - V slash t^2) e^(H - t)$ for every $t > 0$.
]

#proof[
  By Chebyshev, $P(-ln P(X) < H - t) <= V slash t^2$. Every other value has $P(x) <= e^(-H + t)$, so the values of $S$ outside the rare set hold at most $|S| e^(-H + t)$. Hence $p <= V slash t^2 + |S| e^(-H + t)$.
]

#example(title: "Where 1.638 comes from")[
  The search of @sec-search-tree fixes the counts of the large digits first. At the level where $kappa b$ digit positions are still unknown, and $(1 - kappa) b$ digit values are decided, the model says that each decided value appears in the unknown part a Poisson($kappa$) number of times, independently. So the node above a hidden solution has entropy $H = (1 - kappa) b dot H("Poisson"(kappa))$. As a function of $kappa$ this is largest at $kappa approx 0.368$, where it equals $0.4933 b$. The varentropy grows only linearly in $b$, so the proposition gives a bound of $e^(0.4933 b - O(sqrt(b)))$ nodes at that level: about $1.638^b$, since $e^(0.4933) = 1.638$. This is @thm-entropy-bound. By contrast, the exact tree counts every count vector that fits, about $binom(b, kappa b)$ of them, which is largest at $kappa = 1 slash 2$ and grows like $2^b$ (#lib("10.1")).
]
