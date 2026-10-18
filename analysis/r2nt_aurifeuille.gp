\\ Question 31: the M/L series for Aurifeuillian factors of Phi_m(s y^2),
\\ that is of a^n +- b^n with a/b = s y^2.
\\ For squarefree s with discriminant D, m = k |D| / 2 (D even) or m = k |D|
\\ (D odd), k odd, Phi_m(s t^2) = F1(t) F2(t) over Z. At t = y the two values
\\ give L <= M. Claim (gcd(k, D) = 1):
\\   log(M/L) = 2 | sum_{j odd} chi_D(j) c_k(j) / (j s^((j-1)/2) y^j) |
\\ and in general (any k) 2 |sum_{j odd} g(j) / (j s^((j-1)/2) y^j)| with
\\ the twisted Ramanujan sum g below.
\\ usage: gp -q < analysis/r2nt_aurifeuille.gp
default(realprecision, 80); default(parisizemax, 2*10^9);
ramanujan(q, n) = sumdiv(gcd(q, n), r, r * moebius(q / r));
\\ unified: k = m/|D| (D odd) or 2m/|D| (D even), and
\\ g(j) = sum_{r | (j, k)} r mu(k/r) chi_D(k/r) chi_D(j/r)
gfun(s, m, j) = {
  my(D = quaddisc(s), k = if (D % 2, m / abs(D), 2 * m / abs(D)));
  sumdiv(gcd(j, k), r, r * moebius(k / r) * kronecker(D, k / r) * kronecker(D, j / r));
}
series(s, m, y, J) = 2 * sum(i = 0, (J - 1) \ 2, my(j = 2 * i + 1); gfun(s, m, j) / (j * s^((j - 1) / 2) * y^j));
direct(s, m, y) = {
  my(f = factor(polcyclo(m, s * t^2))[, 1]);
  if (#f != 2, return(0));
  log(abs(subst(f[2], t, y) / subst(f[1], t, y)));
}
worst = 0; cnt = 0; worst_simple = 0;
{
for (s = 2, 40, if (!issquarefree(s), next);
  my(D = quaddisc(s));
  for (k = 1, 15, if (k % 2 == 0, next);
    my(m = if (D % 2 == 0, k * abs(D) / 2, k * abs(D)));
    if (m > 240, next);
    for (y = 1, 4,
      my(dl = direct(s, m, y));
      if (dl == 0, print("no split: s=", s, " m=", m); next);
      my(se = series(s, m, y, 401));
      my(e = min(abs(dl - se), abs(dl + se)));
      cnt++; worst = max(worst, e);
      if (gcd(k, D) == 1,
        my(simple = 2 * kronecker(D, k) * sum(i = 0, 200, my(j = 2 * i + 1); kronecker(D, j) * ramanujan(k, j) / (j * s^((j - 1) / 2) * y^j)));
        worst_simple = max(worst_simple, min(abs(dl - simple), abs(dl + simple))));
      if (y == 1 && k <= 3 && s <= 7, print("s=", s, " m=", m, " k=", k, " y=1: M/L = ", precision(exp(abs(dl)),10), "  log = ", precision(abs(dl),10), "  leading term 2 chi(k) mu(k) = ", 2 * kronecker(D, k) * moebius(k))))));
print("cases: ", cnt, "; largest |direct - series| (any k): ", worst, "; largest error of the gcd(k,D)=1 formula: ", worst_simple);
}
\q
