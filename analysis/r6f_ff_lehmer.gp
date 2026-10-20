\\ Round 6, field families: checks of Theorem F.5 and Corollary F.7.
\\
\\ check(x, p, U): with D = 4 p x^x - U^2 > 0 and gcd(x, D) = 1, factor
\\ mu = (U + sqrt(-D))/2 in Q(sqrt(-D)), split (mu) = J A^x (Lemma F.1), and
\\ if J is ambiguous build rho, n and the Lehmer number of Theorem F.5 and
\\ test Step 4: L_n g = +-(f/c). Part 1: artificial U near sqrt(4 p x^x).
\\ Part 2: planted mu = rho^(x/e), so that n > 1. Part 3: the ambiguity
\\ rule of Corollary F.7 against PARI.
\\ Usage: gp -q r6f_ff_lehmer.gp > data/r6f_ff_lehmer.txt
default(parisize, "2G");
ordcls(K, I) = {
  my(c = bnfisprincipal(K, I, 0), cy = K.cyc, o = 1);
  for (i = 1, #cy, o = lcm(o, cy[i] / gcd(cy[i], c[i])));
  o;
}
check(x, p, U) = {
  my(D = 4*p*x^x - U^2, D0, f, K, mu, fa, A, J, conjJ, amb, e, j1, c, J1, t, n, rho, rr, Ln, g, isp);
  if (D <= 0 || gcd(x, D) != 1 || (U - D) % 2, return(0));
  D0 = core(D); f = sqrtint(D / D0);
  K = bnfinit(y^2 + D0, 1);
  mu = Mod((U + f*y)/2, y^2 + D0);
  fa = idealfactor(K, mu);
  A = 1; J = 1;
  for (i = 1, #fa~, my(pr = fa[i,1], v = fa[i,2], a = round(v / x));
    A = idealmul(K, A, idealpow(K, pr, a));
    J = idealmul(K, J, idealpow(K, pr, v - x*a)));
  if (idealnorm(K, A) != x, print("norm A != x at ", [x,p,U]); return(-1));
  conjJ = idealmul(K, idealnorm(K, J), idealinv(K, J));
  amb = (idealhnf(K, J) == idealhnf(K, conjJ));
  e = ordcls(K, A);
  if (!amb, return([x, p, D0, K.cyc, e, "J not ambiguous"]));
  \\ J = c * J1, J1 squarefree product of ramified primes
  J1 = 1; j1 = 1;
  my(fj = idealfactor(K, J));
  for (i = 1, #fj~, my(pr = fj[i,1], v = fj[i,2]);
    if (pr.e == 2 && v % 2, J1 = idealmul(K, J1, pr); j1 *= pr.p));
  c = sqrtint(idealnorm(K, J) / j1);
  my(oJ = ordcls(K, J1));
  t = if (oJ == 1, e, e/2); n = x / t;
  if (denominator(n) != 1 || n % 2 == 0, print("bad n ", [x,p,e,oJ]); return(-1));
  rr = bnfisprincipal(K, idealmul(K, J1, idealpow(K, A, t)));
  if (rr[1] != 0*rr[1], print("not principal"); return(-1));
  rho = Mod(nfbasistoalg(K, rr[2]), y^2 + D0);
  \\ fix the unit: rho^n = eps * j1^((n-1)/2) * mu / c
  my(eps = rho^n / (j1^((n-1)/2) * mu / c));
  if (eps == -1, rho = -rho; eps = 1);
  if (eps != 1, return([x, p, D0, "unit", lift(eps)]));
  my(rb = conj(rho), num = (rho^n - rb^n)/(rho - rb) / j1^((n-1)/2));
  Ln = lift(num);
  g = polcoeff(lift(rho - rb), 1);    \\ rho - rhobar = g sqrt(-D0)
  isp = (Ln * g == f / c) || (Ln * g == -f / c);
  [x, p, D0, K.cyc, e, oJ, n, Ln, f/c, isp];
}

{
  my(cnt = 0, bad = 0);
  forstep (x = 9, 21, 2,
    foreach ([1, 1, 3, 5], p,
      my(S = sqrtint(4*p*x^x));
      for (k = 1, 400,
        my(U = S - k);
        if (p == 3 && U % 3, next);
        if (p == 5 && U % 5, next);
        my(r = check(x, p, U));
        if (type(r) == "t_VEC" && #r == 10,
          cnt++;
          if (!r[10], bad++; print("FAIL ", r));
          if (cnt % 500 == 1, print(r))))));
  print("part 1, artificial ambiguous cases checked: ", cnt, "  failures: ", bad);
}

{
  my(cnt = 0, bad = 0);
  foreach ([7, 11, 19, 23, 31, 39, 47, 55, 71, 87, 95], D0,
    my(K = bnfinit(y^2 + D0, 1));
    forstep (x = 3, 61, 2,
      my(fx = factor(x), ok = 1, A = 1);
      for (i = 1, #fx~, my(dec = idealprimedec(K, fx[i,1]));
        if (#dec < 2, ok = 0; break);
        A = idealmul(K, A, idealpow(K, dec[1], fx[i,2])));
      if (!ok, next);
      my(e = ordcls(K, A));
      if (x % e, next);
      my(rho = Mod(nfbasistoalg(K, bnfisprincipal(K, idealpow(K, A, e))[2]), y^2 + D0));
      my(mu = rho^(x/e), U = lift(trace(mu)));
      if (U < 0, U = -U);
      my(r = check(x, 1, U));
      if (type(r) == "t_VEC" && #r == 10, cnt++;
        if (!r[10], bad++; print("FAIL ", r));
        if (r[7] > 1, print(r)))));
  print("part 2, planted cases checked: ", cnt, "  failures: ", bad);
}

ambJ(x, p, U) = {
  my(D = 4*p*x^x - U^2, D0, f, K, mu, fa, J, conjJ);
  D0 = core(D); f = sqrtint(D / D0);
  K = bnfinit(y^2 + D0, 1);
  mu = Mod((U + f*y)/2, y^2 + D0);
  fa = idealfactor(K, mu);
  J = 1;
  for (i = 1, #fa~, my(pr = fa[i,1], v = fa[i,2], a = round(v / x));
    J = idealmul(K, J, idealpow(K, pr, v - x*a)));
  conjJ = idealmul(K, idealnorm(K, J), idealinv(K, J));
  idealhnf(K, J) == idealhnf(K, conjJ);
}
rule(x, p, q, T, D) = {
  if (gcd(x, D) != 1 || gcd(x, p) != 1, return(0));
  my(fp = factor(p));
  for (i = 1, #fp~, my(l = fp[i,1], k = fp[i,2]);
    if (q % l^ceil(k/2), return(0));
    if (k % 2 && T % l == 0, return(-1)));   \\ -1: rule undecided
  1;
}
{
  my(agree = 0, und = 0, bad = 0);
  foreach ([3, 5, 9, 15, 25, 27, 45, 75], p,
    forstep (x = 7, 13, 2,
      for (q = 0, 30,
        for (k = 0, 6,
          my(b = sqrtint(x^x \ p) - 7*k - 1, U = 2*p*b + q, D = 4*p*x^x - U^2);
          if (D <= 0 || (U - D) % 2, next);
          my(T = x^x - p*b^2 - q*b, r = rule(x, p, q, T, D), a = ambJ(x, p, U));
          if (r == -1, und++; next);
          if (r == a, agree++, bad++; if (r == 1, print("UNSOUND ", [x, p, q, b, r, a])))))));
  print("part 3, rule agrees ", agree, ", undecided ", und, ", rule says no but J ambiguous ", bad);
}
