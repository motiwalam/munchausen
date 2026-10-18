\\ Question 52: b(b+x) = x^n + 1 for x == 0 (mod 8) with an odd prime factor,
\\ all odd n >= 5, each x up to X (section 3 of the round 3 draft).
\\
\\ x = 2^a m, E = (x/2)^2 + 1, K = Q(sqrt E), gamma = (b + x/2 + sqrt E)/2.
\\ Then (gamma) = Q^(a n - 2) B^n with Q a prime above 2 and B of norm m
\\ (Lemma 3.1). With C = Q^a B of class order d, n = n0 + d j where
\\ n0 C == 2 [Q] in the class group, and gamma = +-eta0^k rho eta^j with
\\ (rho) = C^n0 Q^-2 and (eta) = C^d. Then
\\     0 < |2 k mu0 + lam + j th| = Lam0 < tau_n,
\\ lam = log|rho/rho'|, th = log|eta/eta'|.
\\ Matveev's theorem (three logarithms) bounds j by J; the reduction of
\\ Dujella and Petho then leaves j < j0, and those n are checked exactly.
\\ Every odd n <= NDIRECT is also checked exactly.
\\
\\ usage: (echo 'X=2000; CERT=1;'; cat analysis/r3nt_even.gp) | gp -q
default(realprecision, 200);
default(parisizemax, 2*10^9);
if (type(NDIRECT) == "t_POL", NDIRECT = 301);
if (type(CERT) == "t_POL", CERT = 0);
\\ test mode: NMIN = 3 and POW2 = 1 also treat n = 3 and x = 2^a
if (type(NMIN) == "t_POL", NMIN = 5);
if (type(POW2) == "t_POL", POW2 = 0);
\\ Matveev, real case, n = 3 logarithms, degree 2
CM = 1.4 * 30^6 * 3^4.5 * 2^2 * (1 + log(2));
issol(x, n) = issquare(4*x^n + x^2 + 4);
\\ an upper bound for log tau_n, valid for n >= 5 and x >= 24
logtau(x, n) = log(sqrt(x^2 + 4)) - (n/2)*log(x) + 0.01;
emb(K, D, a, s) = subst(lift(a), t, s*sqrt(D));
\\ the largest j that Matveev does not exclude
jmax(x, d, n0, mu0, A2, A3) = {
  my(ok(j) = my(n = n0 + d*j, B = max(j, (j*A2 + A3)/(2*mu0) + 1));
       logtau(x, n) >= -CM * (1 + log(B)) * (2*mu0) * A2 * A3);
  my(lo = 1, hi = 2);
  while (ok(hi), lo = hi; hi *= 2);
  while (hi - lo > 1, my(mid = (lo + hi) \ 2); if (ok(mid), lo = mid, hi = mid));
  lo;
}
dist(r) = abs(r - round(r));
\\ log|g/g'| for g in factored form (a matrix of nf elements and exponents)
lratio(K, fam) = {
  my(s = 0., em);
  for (i = 1, #fam~,
    em = nfeltembed(K, fam[i, 1]);
    s += fam[i, 2] * (log(abs(em[1])) - log(abs(em[2]))));
  s;
}
nconf = 0; nred = 0; worstJ = 0; found = List(); nhard = 0;
{
forstep (x = 8, X, 8,
  my(a = valuation(x, 2), m = x >> valuation(x, 2));
  if ((m == 1 && !POW2) || issquare(x), next);
  my(E = (x/2)^2 + 1, K, D, mu0, Q2, fa, np, cps, prsList);
  \\ exact check of small exponents
  forstep (n = NMIN, NDIRECT, 2, if (issol(x, n), listput(found, [x, n, "direct"])));
  K = bnfinit(t^2 - E, 1);
  if (CERT && bnfcertify(K) != 1, error("certification failed at x = ", x));
  D = E;
  mu0 = K.reg;
  Q2 = idealprimedec(K, 2);
  if (#Q2 != 2, error("2 does not split at x = ", x));
  fa = factor(m); np = #fa~;
  for (iq = 1, 2,
    my(Q = Q2[iq]);
    for (mask = 0, 2^np - 1,
      my(B = 1, C, d, n0s = List());
      for (i = 1, np,
        my(pr = idealprimedec(K, fa[i, 1]));
        B = idealmul(K, B, idealpow(K, pr[1 + bittest(mask, i - 1)], fa[i, 2])));
      C = idealmul(K, idealpow(K, Q, a), B);
      d = 1; while (bnfisprincipal(K, idealpow(K, C, d), 0) != 0, d++);
      for (n0 = 0, d - 1,
        if (bnfisprincipal(K, idealmul(K, idealpow(K, C, n0), idealpow(K, Q, -2)), 0) == 0,
          listput(n0s, n0)));
      for (i0 = 1, #n0s,
        my(n0 = n0s[i0], rho, eta, lam, th, A2, A3, J, kap, mu, cf, p0, q0, p1, q1, eps0, j0, done);
        nconf++;
        \\ generators in compact form (flag 4), so that no precision is lost
        lam = lratio(K, bnfisprincipal(K, idealmul(K, idealpow(K, C, n0), idealpow(K, Q, -2)), 4)[2]);
        th = lratio(K, bnfisprincipal(K, idealpow(K, C, d), 4)[2]);
        \\ reduce into [-mu0, mu0] with units (shifts by 2 mu0)
        lam -= 2*mu0*round(lam/(2*mu0)); th -= 2*mu0*round(th/(2*mu0));
        A2 = d*log(x) + abs(th); A3 = n0*log(x) + log(4) + abs(lam);
        if (th == 0, error("theta = 0 at x = ", x));
        J = jmax(x, d, n0, mu0, A2, A3);
        worstJ = max(worstJ, J);
        \\ |j kap + k + mu| < AA BB^-j with kap = th/(2 mu0), mu = lam/(2 mu0)
        kap = th/(2*mu0); mu = lam/(2*mu0);
        my(AA = exp(log(sqrt(x^2 + 4)) + log(4)) / (2*mu0) * x^(-n0/2), BB = x^(d/2));
        cf = contfrac(kap); p0 = 0; q0 = 1; p1 = 1; q1 = 0; done = 0;
        for (i = 1, #cf,
          my(p2 = cf[i]*p1 + p0, q2 = cf[i]*q1 + q0);
          p0 = p1; q0 = q1; p1 = p2; q1 = q2;
          if (q1 > 6*J,
            eps0 = dist(q1*mu) - J*dist(q1*kap);
            if (eps0 > 0,
              j0 = ceil(log(AA*q1/eps0)/log(BB));
              for (jj = 0, max(j0, 0),
                my(n = n0 + d*jj);
                if (n >= NMIN && n % 2 == 1 && n > NDIRECT && issol(x, n),
                  listput(found, [x, n, "reduced"])));
              nred++; done = 1; break)));
        if (!done, nhard++; listput(found, [x, "reduction failed", iq, mask, n0, d]))));
  );
  if (x % 1000 == 0, print("x = ", x, ": configurations ", nconf, ", largest Matveev bound ", worstJ)));
print("x = 8m <= ", X, " with m > 1 odd, x not a square; exact check of odd n in [5, ", NDIRECT, "]");
print("configurations (Q, B, n0): ", nconf, "; reduced: ", nred, "; failed: ", nhard);
print("largest Matveev bound for j: ", worstJ);
print("solutions or problems: ", found);
}
\q
