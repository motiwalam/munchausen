\\ Question 51: all odd exponents n >= 17 of b(b+x) = x^n + c for odd x up to X,
\\ c = 3 (x prime to 3) or c = 25 (x prime to 5). The method of
\\ analysis/r2nt_allnx.gp (Theorem 18.12) with theta = (x + sqrt D)/2,
\\ D = x^2 + 4c, in place of eps (section 4 of the round 3 draft).
\\ For every choice B of an ideal of norm x with one prime above each p | x,
\\ d is the order of [B]; a solution has d | n, b + theta = u eta^(n/d) with
\\ (eta) = B^d, and |2 k mu0 + (n/d) th| < tau_n, th = log|eta/eta'|,
\\ tau_n = sqrt(D) / (x^(n/2) - x/2 - c). Laurent bounds n/d; the
\\ convergents of th/(2 mu0) give the only candidates (Legendre).
\\ The class groups are certified with bnfcertify. n <= 15: r3nt_sieve.
\\ usage: (echo 'c=3; X=1001;'; cat analysis/r3nt_allnc.gp) | gp -q
default(realprecision, 150);
default(parisizemax, 2*10^9);
if (type(NMIN) == "t_POL", NMIN = 17);
C2 = 403.2;
logtau(x, n) = my(den = x^(n/2) - x/2 - c); if (den <= 1, 10^9, log(sqrt(x^2 + 4*c)) - log(den));
logtauU(x, n) = if (n < 60, logtau(x, n), log(sqrt(x^2 + 4*c)) - (n/2)*log(x) + 0.01);
allowed(x, n, d, mu0, th) = {
  my(lA1 = max(mu0, 1)/2, lA2 = (d*log(x) + abs(th))/2, m = n/d, bp, M);
  bp = (m + 1)/(2*lA2) + m/(2*lA1);
  M = max(log(bp) + 0.38, 5);
  logtauU(x, n) >= -C2 * M^2 * lA1 * lA2;
}
nmax(x, d, mu0, th) = {
  my(lo = max(NMIN, d), hi);
  if (!allowed(x, lo, d, mu0, th), return(lo - 1));
  hi = lo; while (allowed(x, hi, d, mu0, th), hi *= 2);
  while (hi - lo > 1, my(mid = (lo + hi) \ 2); if (allowed(x, mid, d, mu0, th), lo = mid, hi = mid));
  lo;
}
lratio(K, fam) = {
  my(s = 0., em);
  for (i = 1, #fam~, em = nfeltembed(K, fam[i, 1]); s += fam[i, 2] * (log(abs(em[1])) - log(abs(em[2]))));
  s;
}
issol(x, n) = issquare(4*x^n + x^2 + 4*c);
found = List(); maxn = 0; nB = 0; nonprinc = 0; nx = 0; ninert = 0; nleg = 0;
{
forstep (x = 3, X, 2,
  if (x % (if (c == 3, 3, 5)) == 0 || issquare(x), next);
  nx++;
  my(D = x^2 + 4*c, K, mu0, fa, np);
  \\ a solution needs D to be a square mod every p | x (U^2 = 4 x^n + D)
  if (#select(p -> kronecker(D, p) != 1, factor(x)[, 1]), ninert++; next);
  K = bnfinit(w^2 - D, 1);
  if (bnfcertify(K) != 1, error("certification failed at x = ", x));
  mu0 = K.reg;
  fa = factor(x); np = #fa~;
  for (mask = 0, 2^np - 1,
    my(B = 1, d, th, nh, cf, p0 = 0, q0 = 1, p1 = 1, q1 = 0);
    for (i = 1, np,
      my(pr = idealprimedec(K, fa[i, 1]));
      if (#pr != 2, error("p does not split at x = ", x));
      B = idealmul(K, B, idealpow(K, pr[1 + bittest(mask, i - 1)], fa[i, 2])));
    nB++;
    d = 1; while (bnfisprincipal(K, idealpow(K, B, d), 0) != 0, d++);
    if (d > 1, nonprinc++);
    if (d % 2 == 0, next);
    th = lratio(K, bnfisprincipal(K, idealpow(K, B, d), 4)[2]);
    th -= 2*mu0*round(th/(2*mu0));
    nh = nmax(x, d, mu0, th);
    maxn = max(maxn, nh);
    \\ Legendre: (n/d) tau_n < mu0 for every n >= max(NMIN, d), since n tau_n decreases
    if (max(NMIN, d)/d * exp(logtauU(x, max(NMIN, d))) >= mu0 && nh >= max(NMIN, d),
      if (NMIN >= 17, error("Legendre condition fails at x = ", x), nleg++));
    cf = contfrac(th / (2*mu0));
    for (j = 1, #cf,
      my(p2 = cf[j]*p1 + p0, q2 = cf[j]*q1 + q0);
      p0 = p1; q0 = q1; p1 = p2; q1 = q2;
      if (d*q1 > nh, break);
      if (j == #cf, error("continued fraction too short at x = ", x));
      if (q1 % 2 == 0, next);
      my(r = abs(q1*th - 2*p1*mu0));
      forstep (g = 1, nh \ (d*q1), 2,
        my(n = d*g*q1);
        if (log(g*r) >= logtauU(x, n), break);
        if (n >= NMIN, listput(found, [x, n, mask, d, if (n < 3000, issol(x, n), "unchecked")])))));
);
print("c = ", c, ": ", nx, " odd x <= ", X, " (not squares, prime to ", if (c == 3, 3, 5), "); ",
      ninert, " excluded because some p | x does not split; ",
      nB, " ideals B, ", nonprinc, " not principal; largest n allowed by Laurent: ", maxn);
if (nleg, print("test mode: Legendre condition not met for ", nleg, " ideals"));
print("candidates with n >= ", NMIN, " [x, n, choice, d, is a solution]: ", found);
}
\q
