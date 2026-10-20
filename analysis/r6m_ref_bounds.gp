\\ Referee recomputation of the bounds of chapter 38, written separately
\\ from r6m_square_bounds.py and r6m_lead_bounds.py.
\\ Usage: gp -q -s 2G r6m_ref_bounds.gp < /dev/null
\\
\\ Part 1. The gaps of Theorem 38.2.
\\ f(t) = 2 k^a sinh t (e odd) or 2 k^a cosh t (e even); T = 2ke.
\\ g- = T - finv(floor f(T)), g+ = finv(floor f(T) + 1) - T,
\\ X_sq = sqrt(2 e k^3 / g-). The precision is doubled until the
\\ fractional part of f(T) is clear of 0 and 1, so N0 is right.
gaps(k, e, a) = {
  my(T = 2*k*e, d = ceil(T/2.30) + 50, f, N0, fr, gm, gp, X, ok = 0);
  while (!ok,
    localprec(d);
    f = if (e % 2, 2*k^a*sinh(T), 2*k^a*cosh(T));
    N0 = floor(f); fr = f - N0;
    if (fr > 10^-20 && fr < 1 - 10^-20, ok = 1, d *= 2));
  localprec(d);
  my(finv = if (e % 2, v -> asinh(v/(2*k^a)), v -> acosh(v/(2*k^a))));
  gm = T - finv(N0); gp = finv(N0 + 1) - T;
  X = sqrt(2*e*k^3/gm);
  printf("k=%d e=%d a=%d T=%d digits=%d frac=%.8g g-=%.8g g+=%.8g X_sq=%.10g\n",
         k, e, a, T, d, fr, gm, gp, X);
}
print("# Theorem 38.2: gaps and X_sq");
gaps(1, 1, 0);
gaps(5, 1, 0);
gaps(9, 2, 1);
gaps(32, 5, 2);
gaps(125, 3, 1);
gaps(2401, 4, 1);

\\ Part 2. Theorem 38.7: b(xb+1) = x^x + 1, x even, R = 4x+1 not a square,
\\ Lam0 = (x+1) log alpha - 2j log eta > 0. Laurent (m, C2) = (10, 25.2), D = 2:
\\   -log Lam0 <= 25.2*16*M^2 logA1 logA2, M = max(log b' + 0.38, 5),
\\   logA1 = max(reg,1)/2, logA2 = h(alpha) = (1/2) log(x alpha),
\\   b' = 2j/(2 logA2) + (x+1)/(2 logA1), 2j <= (x+1) log alpha / reg.
\\ The right side is maximized over reg = log eta in
\\ [log((1+sqrt5)/2), (sqrt R/2)(log R + 2)] on a geometric grid of 2001 points.
default(realprecision, 60);
lrhs(x, reg) = {
  my(R = 4*x+1, s = sqrt(R), la = log((s+1)/(s-1)), lA2 = log(x*(s+1)/(s-1))/2,
     lA1 = max(reg, 1)/2, bp = (x+1)*la/reg/(2*lA2) + (x+1)/(2*lA1),
     M = max(log(bp) + 0.38, 5));
  403.2*M^2*lA1*lA2;
}
llhs(x) = {
  my(R = 4*x+1, s = sqrt(R), L = log(2) + (x+1)/2*log(x));
  \\ log(U - s) >= log(2 x^((x+1)/2) - s) = L + log(1 - s/exp(L))
  L + if (L > 200, -10^-40, log(1 - s*exp(-L))) - log(2*s);
}
lworst(x) = {
  my(R = 4*x+1, rmax = sqrt(R)/2*(log(R)+2), r0 = log((1+sqrt(5))/2), best = 0);
  for (i = 0, 2000, my(reg = r0 * (rmax/r0)^(i/2000)); best = max(best, lrhs(x, reg)));
  best;
}
lallowed(x) = llhs(x) <= lworst(x);
{
  print("# Theorem 38.7: Laurent bound");
  my(lo = 10^6, hi = 10^13);
  if (!lallowed(lo) || lallowed(hi), error("bracket"));
  for (i = 1, 120, my(mid = sqrtint(lo*hi)); if (lallowed(mid), lo = mid, hi = mid));
  printf("largest allowed even x about %.8g\n", lo*1.);
  my(x = 4265*10^8);
  printf("at x = 4.265e11: lhs = %.10g  rhs at the largest log eta = %.10g  max over the grid = %.10g\n",
         llhs(x), lrhs(x, sqrt(4*x+1)/2*(log(4*x+1)+2)), lworst(x));
}

\\ Part 3. Theorem 38.6. Field case (i): r = 1 + |S| logs from a Minkowski
\\ basis plus log|theta/theta'|, s = r + 1, Matveev real case D = 2, with
\\ |S| = 2 omega(Aq) and max((log l)^2, 2 log l) per prime (worst case).
\\ Square case (ii): t = 1 + omega(Aq) logs over Q, D = 1. In logs, x = exp(lx).
default(realprecision, 50);
w(d, m) = if (d == 0, m, d^d);
Cm(s, D) = 1.4 * 30^(s+3) * s^4.5 * D^2 * (1 + log(D));
field(lx, A, q, ns, prodlog) = {
  my(r = 1 + ns, s = r + 1, Vr = Pi^(r/2)/gamma(r/2+1), Kr = 2^r/Vr,
     x = exp(lx), R = q^2 + 4*x*A, hreg = sqrt(R)*(log(4*R) + 2),
     cov = sqrt(2 + ns) * hreg * prodlog,
     prodA = (sqrt(r+1)/2)^r * Kr * cov,
     Ath = lx + log(A) + 1,
     B = Kr * max(x + 1, Kr*sqrt(r+1)/0.96*4*(x+1)*(2*lx + log(A))),
     L = (x+1)/2*lx - log(3*sqrt(R)) - log(Kr));
  if (L <= 0, return(1));
  log(Cm(s, 2)) + log(1 + log(B)) + log(prodA) + log(Ath) - log(L);
}
split(lx, A, q) = {
  my(f = factor(A*q)[,1], s = 1 + #f, x = exp(lx),
     pl = prod(i = 1, #f, log(f[i])),
     Ath = lx + log(A) + 1,
     B = 4*(x+1)*(lx + log(A))/log(2) + x + 1,
     L = (x+1)/2*lx - log(3*sqrt(q^2 + 4*x*A)));
  if (L <= 0, return(1));
  log(Cm(s, 1)) + log(1 + log(B)) + log(pl) + log(Ath) - log(L);
}
bis(F) = {
  my(lo = 5., hi = 2000.);
  if (F(lo) <= 0, return(0));
  for (i = 1, 80, my(mid = (lo + hi)/2); if (F(mid) > 0, lo = mid, hi = mid));
  hi / log(10);
}
fam(q, r, m) = {
  my(A = w(q, m) + w(r, m) - r, f = factor(A*q)[,1], ns = 2*#f,
     pl = prod(i = 1, #f, max(log(f[i])^2, 2*log(f[i]))));
  [A, ns, bis(lx -> field(lx, A, q, ns, pl)), bis(lx -> split(lx, A, q))];
}
{
  print("# Theorem 38.6: log10 of the bounds, 1 <= q <= 20, 0 <= r <= 20");
  my(worst = [0], worstsplit = 0, v, n = 0);
  for (q = 1, 20, for (r = 0, 20, foreach(if (r == 0, [0, 1], [1]), m,
    v = fam(q, r, m); n++;
    if (v[3] > worst[1], worst = [v[3], q, r, m, v[1], v[2]]);
    worstsplit = max(worstsplit, v[4]))));
  printf("%d families\n", n);
  printf("worst field case: log10 X = %.2f at (x,%d,%d) m=%d A=%d |S|=%d\n",
         worst[1], worst[2], worst[3], worst[4], worst[5], worst[6]);
  printf("worst square case: log10 X = %.2f\n", worstsplit);
  foreach([[1,1,1],[1,0,0],[1,2,1],[1,7,1],[20,4,1]], t, v = fam(t[1], t[2], t[3]);
    printf("(x,%d,%d) m=%d: A=%d |S|=%d log10 X field %.2f square %.2f\n",
           t[1], t[2], t[3], v[1], v[2], v[3], v[4]));
}
