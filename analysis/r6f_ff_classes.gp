\\ Round 6, field families: the size of the obstruction in each regime.
\\
\\ last, x odd (imaginary): K = Q(sqrt(-D)), D = 4p(x - W) - q^2. Reports the
\\   class number h, the order e of the class of an ideal A of norm x (one
\\   prime above each l | x, the first in PARI's order), and e / sqrt(x).
\\   Only x with every prime of x split are used (the others are excluded
\\   locally).
\\ mid, x odd (real): K = Q(sqrt(x^2 + 4pA)). Reports h, the regulator
\\   Reg, and Reg / log x.
\\ lead, x even (real): K = Q(sqrt(q^2 + 4xA)) and Q(sqrt(x)). Reports
\\   the two regulators divided by sqrt(x).
\\ Usage: gp -q r6f_ff_classes.gp > data/r6f_ff_classes.txt
\\ (quadclassunit assumes GRH; the numbers are illustrations only)
default(parisize, "1G");
w(d, m) = if (d == 0, m, d^d);
formorder(f, h) = {
  my(id = qfbpow(f, 0));
  fordiv (h, d, if (qfbpow(f, d) == id, return(d)));
  -1;
}
lastrow(p, q, x) = {
  my(W = w(p, 1) + w(q, 1), D = 4*p*(x - W) - q^2, Delta, h, fx, A, e);
  if (D <= 0, return(0));
  Delta = coredisc(-D); h = qfbclassno(Delta);
  fx = factor(x); A = qfbpow(qfbprimeform(Delta, 1), 0);
  for (i = 1, #fx~, my(l = fx[i,1]);
    if (kronecker(Delta, l) != 1, return(0));
    A = qfbcomp(A, qfbpow(qfbprimeform(Delta, l), fx[i,2])));
  e = formorder(A, h);
  [h, e];
}
{
  print("# last, x odd: p q window, count, mean h/sqrt(x), mean e/sqrt(x), max e/sqrt(x), share e = h");
  foreach ([[1,0],[1,1],[1,2],[1,3],[2,1],[3,2],[7,3]], pq,
    foreach ([10^4, 10^6, 10^8], X,
      my(n = 0, sh = 0., se = 0., me = 0., full = 0);
      forstep (x = X + 1, X + 4000, 2,
        my(r = lastrow(pq[1], pq[2], x));
        if (r == 0, next);
        n++; sh += r[1] / sqrt(x); se += r[2] / sqrt(x);
        me = max(me, r[2] / sqrt(x)); full += (r[1] == r[2]));
      if (n, printf("%d %d %d %d %.3f %.3f %.3f %.2f\n", pq[1], pq[2], X, n, sh/n, se/n, me, full/n))));
}
{
  print("# mid, x odd: p q window, count, mean h/(x/log x), mean Reg/log x, share Reg < 3 log x");
  foreach ([[1,1],[1,2],[2,1],[3,2]], pq,
    my(A = w(pq[1], 1) + w(pq[2], 1) - pq[2]);
    foreach ([10^4, 10^6], X,
      my(n = 0, sh = 0., sr = 0., small = 0);
      forstep (x = X + 1, X + 400, 2,
        my(Delta = coredisc(x^2 + 4*pq[1]*A), c = quadclassunit(Delta), R = c.reg, h = c.no);
        n++; sh += h / (x / log(x)); sr += R / log(x); small += (R < 3 * log(x)));
      printf("%d %d %d %d %.3f %.2f %.2f\n", pq[1], pq[2], X, n, sh/n, sr/n, small/n)));
}
{
  print("# lead, x even: q r window, count, mean Reg1/sqrt(x) for q^2+4xA, mean Reg2/sqrt(x) for x, share min < x^(1/3)");
  foreach ([[1,1],[1,2],[2,1],[3,2]], qr,
    my(A = w(qr[1], 1) + w(qr[2], 1) - qr[2]);
    foreach ([10^4, 10^6], X,
      my(n = 0, s1 = 0., s2 = 0., small = 0);
      forstep (x = X, X + 400, 2,
        my(R0 = qr[1]^2 + 4*x*A);
        if (issquare(x) || issquare(R0), next);
        my(R1 = quadclassunit(coredisc(qr[1]^2 + 4*x*A)).reg, R2 = quadclassunit(coredisc(x)).reg);
        n++; s1 += R1 / sqrt(x); s2 += R2 / sqrt(x); small += (min(R1, R2) < x^(1/3)));
      printf("%d %d %d %d %.3f %.3f %.2f\n", qr[1], qr[2], X, n, s1/n, s2/n, small/n)));
}
