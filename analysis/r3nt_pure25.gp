\\ Question 51: pure solutions of b(b+x) = x^n + 25 for odd x prime to 5,
\\ odd n >= 17 (Theorem 4.5, part B, of the round 3 draft).
\\ A pure solution satisfies |n l - s mu0| < tau_n with l = arcsinh(10/x),
\\ mu0 the regulator of Q(sqrt(x^2+100)) and
\\ tau_n = sqrt(x^2+100) / (x^(n/2) - x/2 - 25). Laurent's theorem gives
\\ n <= nhi(x). Since 2 n tau_n < mu0, s/n in lowest terms p/q is a
\\ convergent of l/mu0 (Legendre), and |q l - p mu0| < tau_q. The script
\\ tests every convergent with q <= nhi(x) and prints the candidates.
\\ quadregulator uses continued fractions, so no GRH is involved.
\\ n <= 15 is covered by the sieve (r3nt_sieve with exponent n).
\\ usage: (echo 'X0=3; X1=507211;'; cat analysis/r3nt_pure25.gp) | gp -q
default(realprecision, 80);
C2 = 403.2;
\\ log tau_n, or a huge value when the bound (2) is void (small n)
logtau(x, n) = my(den = x^(n/2) - x/2 - 25); if (den <= 1, 10^9, log(sqrt(x^2 + 100)) - log(den));
\\ an upper bound for log tau_n that avoids huge powers
logtauU(x, n) = if (n < 60, logtau(x, n), log(sqrt(x^2 + 100)) - (n/2)*log(x) + 0.01);
allowed(x, n, mu0, l) = {
  my(lA1 = max(mu0, 1)/2, lA2 = log(x) + l, s, bp, M, lt = logtauU(x, n));
  s = (n*l + 1)/mu0;
  bp = 2*s/(2*lA2) + n/(2*lA1);
  M = max(log(bp) + 0.38, 5);
  lt + log(2) >= -C2 * M^2 * lA1 * lA2;
}
nhi(x, mu0, l) = {
  my(lo = 17, hi);
  if (!allowed(x, lo, mu0, l), return(lo - 2));
  hi = lo; while (allowed(x, hi, mu0, l), hi *= 2);
  while (hi - lo > 1, my(mid = (lo + hi) \ 2); if (allowed(x, mid, mu0, l), lo = mid, hi = mid));
  lo;
}
cnt = 0; maxn = 0; cands = List();
{
forstep (x = X0 + (X0 % 2 == 0), X1, 2,
  if (x % 5 == 0 || issquare(x), next);
  cnt++;
  my(mu0 = quadregulator(coredisc(x^2 + 100)), l = asinh(10/x), nh, cf, p0 = 0, q0 = 1, p1 = 1, q1 = 0);
  nh = nhi(x, mu0, l);
  maxn = max(maxn, nh);
  if (2*17*exp(logtau(x, 17)) >= mu0, error("Legendre condition fails at x = ", x));
  cf = contfrac(l / mu0);
  for (j = 1, #cf,
    my(p2 = cf[j]*p1 + p0, q2 = cf[j]*q1 + q0);
    p0 = p1; q0 = q1; p1 = p2; q1 = q2;
    if (q1 > nh, break);
    if (j == #cf, error("continued fraction too short at x = ", x));
    if (q1 % 2 == 0, next);
    if (log(abs(q1*l - p1*mu0)) < logtauU(x, q1),
      \\ the odd multiples n = g q1 with g |q1 l - p1 mu0| < tau_n
      forstep (g = 1, nh \ q1, 2,
        my(n = g*q1);
        if (log(g*abs(q1*l - p1*mu0)) >= logtauU(x, n), break);
        if (n >= 17, listput(cands, [x, n, if (n < 2000, issquare(4*x^n + x^2 + 100), "unchecked")])))));
);
print("odd x in [", X0, ", ", X1, "] prime to 5, not squares: ", cnt, "; largest n allowed by Laurent: ", maxn);
print("candidates [x, n, is a solution]: ", cands);
}
\q
