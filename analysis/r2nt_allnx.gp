\\ Question 32: all exponents n for each odd non-square x <= X (section 1.6).
\\ For K = Q(sqrt(x^2+4)) and every choice B of a divisor of (x) of norm x
\\ with one prime above each p | x (Lemma 1.3), let d be the order of [B].
\\ A solution with n odd has d | n, b + eps = u eta^(n/d) with (eta) = B^d,
\\ and 0 < 2 k mu0 + (n/d) theta < tau_n, theta = log|eta/eta'|.
\\ Theorem 1.10 bounds n/d; the convergents of theta/(2 mu0) give the only
\\ candidates with n >= 17; every candidate is checked exactly.
\\ n <= 15 and even n are covered elsewhere (r2nt_pure.py, Proposition 1.1).
\\ The class groups are certified with bnfcertify.
\\ usage: (echo 'X=1001;'; cat analysis/r2nt_allnx.gp) | gp -q
\\ (set X0 to start above 3)
default(realprecision, 120);
default(parisizemax, 4*10^9);
C2 = 403.2;
logtau(x, n) = log(sqrt(x^2 + 4)) - log(x^(n/2) - x/2 - 1);
\\ Theorem 1.10 inequality, true if Laurent does not exclude exponent n
allowed(x, n, d, mu0) = {
  my(lA1 = max(mu0, 1)/2, lA2 = (d*log(x) + mu0)/2, m = n/d, bp, M);
  bp = (m + 1)/(2*lA2) + m/(2*lA1);
  M = max(log(bp) + 0.38, 5);
  logtau(x, n) >= -C2 * M^2 * lA1 * lA2;
}
nmax(x, d, mu0) = {
  my(lo = 17, hi);
  if (!allowed(x, lo, d, mu0), return(lo - 2));
  hi = lo; while (allowed(x, hi, d, mu0), hi *= 2);
  while (hi - lo > 1, my(mid = (lo + hi) \ 2); if (allowed(x, mid, d, mu0), lo = mid, hi = mid));
  lo;
}
issol(x, n) = issquare(4*x^n + x^2 + 4);
found = List(); maxq = 0; nB = 0; nonprinc = 0;
{
if (type(X0) == "t_POL", X0 = 3);
for (x = X0, X, if (x % 2 == 0 || issquare(x), next);
  my(D = x^2 + 4, K, eps, P, fa, pr, B0, mu0, emb, h);
  K = bnfinit(w^2 - D, 1);
  if (bnfcertify(K) != 1, error("certification failed at x = ", x));
  h = K.no;
  eps = Mod((x + w)/2, w^2 - D);
  P = idealhnf(K, lift(eps) + 1);
  mu0 = abs(log(abs(subst(lift(K.fu[1]), w, sqrt(D)))));
  fa = factor(x);
  \\ for each p | x the prime pi_p dividing P and its conjugate
  my(np = #fa~, prs = vector(np), cps = vector(np));
  for (i = 1, np,
    pr = idealprimedec(K, fa[i, 1]);
    if (#pr != 2, error("p does not split"));
    if (idealval(K, P, pr[1]) > 0, prs[i] = pr[1]; cps[i] = pr[2], prs[i] = pr[2]; cps[i] = pr[1]));
  for (mask = 0, 2^np - 1,
    my(B = 1, d, eta, th, q, cf, nh, conv, e1, e2);
    for (i = 1, np, B = idealmul(K, B, idealpow(K, if (bittest(mask, i - 1), prs[i], cps[i]), fa[i, 2])));
    nB++;
    \\ order of the class of B
    d = 1; while (bnfisprincipal(K, idealpow(K, B, d), 0) != 0 && d <= h, d++);
    if (d > 1, nonprinc++);
    if (d % 2 == 0, next);      \\ d must divide the odd n
    eta = bnfisprincipal(K, idealpow(K, B, d), 1)[2];
    eta = nfbasistoalg(K, eta);
    e1 = subst(lift(eta), w, sqrt(D)); e2 = subst(lift(eta), w, -sqrt(D));
    th = log(abs(e1 / e2));
    nh = nmax(x, d, mu0);
    \\ convergents p/q of th/(2 mu0); need |q th + 2 k mu0| < tau_(d q)
    cf = contfrac(th / (2*mu0));
    my(p0 = 0, q0 = 1, p1 = 1, q1 = 0);
    for (j = 1, #cf,
      my(p2 = cf[j]*p1 + p0, q2 = cf[j]*q1 + q0);
      p0 = p1; q0 = q1; p1 = p2; q1 = q2;
      if (d*q1 > nh, break);
      maxq = max(maxq, d*q1);
      if (q1 % 2 == 0, next);
      my(n = d*q1);
      if (n < 17, next);
      if (abs(q1*th - p1*2*mu0) < exp(logtau(x, n)) + 10^-60,
        listput(found, [x, n, mask, d, issol(x, n)])));
    );
  if (x % 100 == 1, print("x = ", x, " done; ideals ", nB, ", non-principal ", nonprinc, ", largest n tested ", maxq)));
print("x from ", X0, " to ", X, ": ", nB, " ideals B, ", nonprinc, " non-principal, largest n allowed by Laurent ", maxq);
print("candidates with n >= 17 (x, n, choice, d, is a solution): ", found);
}
\q
