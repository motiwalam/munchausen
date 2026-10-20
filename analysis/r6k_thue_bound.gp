\\ Round 6, k-length: the 3-adic bound of Theorem K.4 (question 131).
\\
\\ A 4-digit string (p, q, r, x) with x last and a binomial prefix,
\\ q^2 = 3 p r, is a solution in base b exactly when
\\
\\     Y^3 - 27 p^2 x^x = R0,   Y = 3 p b + q,   R0 = q^3 + 27 p^2 (W - x),
\\
\\ W = w(p) + w(q) + w(r). For 3 | x put X = x^(x/3), p^2 = n f^3 with n
\\ cube-free, V = 3 f X: Y^3 - n V^3 = R0, a Thue equation in the fixed
\\ field K = Q(n^(1/3)). beta = Y - alpha V (alpha = n^(1/3)) has norm R0,
\\ and sigma(beta) - beta = (1 - omega) alpha V with v_3(V) >= 1 + x/3.
\\ With beta = delta eta^m (eta > 1 a unit of K, delta balanced), the
\\ bound of Bugeaud and Laurent for two 3-adic logarithms (Theorem 32.1)
\\ gives, for a_1 = sigma(delta)/delta, a_2 = sigma(eta)/eta independent,
\\
\\   x/3 + 3/2 - log_3|R0| <= C g D^4 max(log b' + log log 3 + 0.4, 10)^2
\\                            log A1 log A2,
\\   C = 24 * 3 / (2 (log 3)^4),  g <= 3^fL - 1,  D in {3, 6},
\\   log A1 = max((2/3)(log|R0| + log eta), log 3 / D),
\\   log A2 = max((2/3) log eta, log 3 / D),
\\   b' = 1/(D log A2) + M/(D log A1),
\\   M = (log 3 + 2 log(alpha V + 1)) / log eta + 1/2.
\\
\\ |R0| is replaced by its upper bound q^3 + 27 p^2 (W + x). The script
\\ prints the largest x for which the inequality can hold, and the side
\\ bound of the proof for dependent a_1, a_2. The unit eta is the one
\\ bnfinit returns; the proof needs only that it is a unit (checked).
\\
\\ usage: gp -q r6k_thue_bound.gp      (families with p, q, r <= 20)

default(realprecision, 60);
W(d, m) = if(d == 0, m, d^d);

cubefree(N) = {
  my(F = factor(N), n = 1, f = 1);
  for(i = 1, #F~, my(l = F[i,1], e = F[i,2]); n *= l^(e % 3); f *= l^(e \ 3));
  [n, f];
}

\\ field data for n: [log eta, fL, wL]
fielddata(n) = {
  my(bnf = bnfinit(t^3 - n, 1), u, al, val, nfL, P);
  al = sqrtn(n * 1., 3);
  u = lift(nfbasistoalg(bnf, bnf.fu[1]));
  if(abs(norm(Mod(u, t^3 - n))) != 1, error("not a unit"));
  if(denominator(content(u)) != 1 && 0, error("check integrality"));
  val = subst(u, t, al);
  nfL = nfinit(nfsplitting(t^3 - n));
  P = idealprimedec(nfL, 3);
  [abs(log(abs(val))), vecmax(vector(#P, i, P[i].f)), nfrootsof1(nfL)[1]];
}

\\ the main inequality at x (real), D, g; returns RHS - LHS
gap(x, p, q, Wt, n, f, le, D, g) = {
  my(R = q^3 + 27 * p^2 * (Wt + x), lR = log(R), la1, la2, M, bp, C);
  la1 = max((2/3) * (lR + le), log(3) / D);
  la2 = max((2/3) * le, log(3) / D);
  M = (log(3) + 2 * (log(3 * f) + log(n) / 3 + (x / 3) * log(x) + 1e-14)) / le + 1/2;
  \\ log(alpha V + 1) <= log(alpha V) + 1e-14 since alpha V >= 3 * 30^10 for x >= 30
  bp = 1 / (D * la2) + M / (D * la1);
  C = 24 * 3 * g / (2 * log(3)^4) * D^4;
  C * max(max(log(bp) + log(log(3)) + 0.4, 10 * log(3) / D), 10)^2 * la1 * la2
    - (x / 3 + 3/2 - lR / log(3));
}

\\ largest x with gap >= 0 (the gap is negative for all larger x)
largest(p, q, Wt, n, f, le, D, g) = {
  my(lo = 30., hi = 1e40);
  if(gap(hi, p, q, Wt, n, f, le, D, g) >= 0, error("bound above 1e40"));
  if(gap(lo, p, q, Wt, n, f, le, D, g) < 0, return(lo));
  while(hi / lo > 1 + 1e-12, my(mid = sqrt(lo * hi));
    if(gap(mid, p, q, Wt, n, f, le, D, g) >= 0, lo = mid, hi = mid));
  hi;
}

\\ side case: a_1, a_2 dependent; x/3 + 3/2 - log_3|R0| <= c + log_3(w N)
side(x, p, q, Wt, n, f, le, fL, wL) = {
  my(R = q^3 + 27 * p^2 * (Wt + x), G = 3^fL - 1, hg = (2/3) * le, k2, c, M, Np);
  k2 = hg / (2 / (6 * log(18)^3));
  c = 6 * (9 * G * hg + log(2)) / log(3);
  M = (log(3) + 2 * (log(3 * f) + log(n) / 3 + (x / 3) * log(x))) / le + 1/2;
  Np = k2 * (M + 1/2);
  c + log(wL * Np) / log(3) - (x / 3 + 3/2 - log(R) / log(3));
}
sidelargest(p, q, Wt, n, f, le, fL, wL) = {
  my(lo = 30., hi = 1e40);
  if(side(lo, p, q, Wt, n, f, le, fL, wL) < 0, return(lo));
  while(hi / lo > 1 + 1e-12, my(mid = sqrt(lo * hi));
    if(side(mid, p, q, Wt, n, f, le, fL, wL) >= 0, lo = mid, hi = mid));
  hi;
}

{
  my(B = 20, fams = List(), cache = Map(), worst = 0);
  for(p = 1, B, for(q = 0, B, for(r = 0, B,
    if(q^2 == 3 * p * r && !ispower(p, 3), listput(fams, [p, q, r])))));
  print("# p q r m n f log_eta fL wL X_T(D=3) X_T(D=6) X_side");
  foreach(fams, F,
    my(p = F[1], q = F[2], r = F[3], nf = cubefree(p^2), n = nf[1], f = nf[2], fd, le, fL, wL);
    if(!mapisdefined(cache, n), mapput(cache, n, fielddata(n)));
    fd = mapget(cache, n); le = fd[1]; fL = fd[2]; wL = fd[3];
    foreach(if(q == 0 || r == 0, [0, 1], [1]), m,
      my(Wt = W(p, m) + W(q, m) + W(r, m), X3, X6, Xs);
      X3 = largest(p, q, Wt, n, f, le, 3, 3^fL - 1);
      X6 = largest(p, q, Wt, n, f, le, 6, 3^fL - 1);
      Xs = sidelargest(p, q, Wt, n, f, le, fL, wL);
      worst = max(worst, max(X3, max(X6, Xs)));
      printf("%d %d %d %d %d %d %.6f %d %d %d %d %d\n", p, q, r, m, n, f, le, fL, wL, ceil(X3), ceil(X6), ceil(Xs))));
  printf("# largest bound %d\n", ceil(worst));
}
quit;
