\\ Referee checks of chapter 38 on artificial equations, written separately
\\ from r6m_square_check.gp and r6m_lead_check.gp.
\\ (a) Middle, pA = k^2: p b^2 + x b - A = x^n, x odd, prime to k.
\\     For x a prime power: the ideal of w = (mu/mu')^e z^(-s e n) is
\\     (theta/k)^a for one sign s, and k^a Tr(w) is a rational integer
\\     (Lemma 38.1, Step 1 of Theorem 38.2). For omega(x) >= 2 (negative
\\     control) the unit should be absent.
\\ (b) Leading: x b^2 + q b - A = x^n, x even, N(mu) = x^(n+1). The ideal
\\     of mu / theta^(n+1) has support above the primes of A q (Lemma 38.5).
default(parisize, 10^8);
ea(p, k) = {
  if (p == 1, return([1, 0]));
  for (e = 1, 60, for (a = 0, 120,
    my(ok = 1);
    foreach(factor(k)[,1], l, if (e*valuation(p, l) != a*valuation(k, l), ok = 0));
    if (ok, return([e, a]))));
  0;
}
checkmid(p, A, X, NMAX, PP) = {
  my(k = sqrtint(p*A), [e, a] = ea(p, k), cnt = 0, bad = 0);
  forstep (x = 3, X, 2,
    if (gcd(x, k) > 1 || (PP && !isprimepower(x)) || (!PP && omega(x) < 2), next);
    for (n = 2, NMAX,
      my(D = x^2 + 4*p*(x^n + A), U);
      if (!issquare(D, &U), next);
      if ((U - x) % (2*p), next);
      my(R = x^2 + 4*k^2);
      if (issquare(R), next);
      \\ mu = p b + theta = (U + sqrt R)/2, mu' = p b + theta'
      my(K = bnfinit(y^2 - R, 1), th = Mod((x + y)/2, y^2 - R),
         mu = Mod((U + y)/2, y^2 - R), mup = Mod((U - y)/2, y^2 - R),
         z = (th + k)/(th - k), found = 0);
      foreach([1, -1], s,
        my(wv = (mu/mup)^e * z^(-s*e*n),
           I = idealdiv(K, idealhnf(K, lift(wv)), idealpow(K, idealhnf(K, lift(th)/k), a)));
        if (I == idealhnf(K, 1),
          my(T = k^a * trace(wv));
          if (type(T) == "t_INT", found = 1)));
      cnt++;
      if (PP && !found, print("  no unit: p=", p, " A=", A, " x=", x, " n=", n));
      if (!found, bad++)));
  printf("  p=%d A=%d k=%d (e,a)=(%d,%d): %d solutions, %d without the unit\n", p, A, k, e, a, cnt, bad);
}
checklead(Xmax, Qmax, Amax, NMAX) = {
  my(cnt = 0, bad = 0);
  forstep (x = 2, Xmax, 2, for (q = 1, Qmax, for (A = 1, Amax, for (n = 3, NMAX,
    my(D = q^2 + 4*x*(x^n + A), U);
    if (!issquare(D, &U) || (U - q) % (2*x), next);
    my(R = q^2 + 4*x*A);
    if (issquare(R), next);
    my(K = nfinit(y^2 - R), th = (q + y)/2, mu = (U + y)/2,
       F = idealfactor(K, idealdiv(K, idealhnf(K, mu), idealpow(K, idealhnf(K, th), n + 1))), ok = 1);
    for (i = 1, #F~, if ((A*q) % F[i,1].p != 0, ok = 0));
    cnt++;
    if (!ok, bad++; print("  support outside A q: x=", x, " q=", q, " A=", A, " n=", n))))));
  printf("  %d solutions, %d with support outside A q\n", cnt, bad);
}
print("(a) x an odd prime power prime to k, x <= 400, 2 <= n <= 9");
checkmid(1, 1, 400, 9, 1);
checkmid(1, 25, 400, 9, 1);
checkmid(3, 27, 400, 9, 1);
checkmid(3, 3, 400, 9, 1);
checkmid(5, 125, 400, 9, 1);
checkmid(1, 9, 400, 9, 1);
checkmid(2, 8, 400, 9, 1);
print("(a') negative control, omega(x) >= 2, x <= 3000, 2 <= n <= 5");
checkmid(1, 1, 3000, 5, 0);
checkmid(3, 27, 3000, 5, 0);
checkmid(1, 25, 3000, 5, 0);
print("(b) leading, x even <= 1000, q <= 7, A <= 60, 3 <= n <= 9");
checklead(1000, 7, 60, 9);
