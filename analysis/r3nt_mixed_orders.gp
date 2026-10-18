\\ Question 53: orders of the classes of mixed ideals B of norm x in
\\ K = Q(sqrt(x^2 + 4)), for odd non-square x with at least two prime factors.
\\ B is a product over p^a || x of q_p^a with q_p one of the two primes above
\\ p (Lemma 18.3); B is mixed if it is neither P = (eps + 1) nor its
\\ conjugate. B and its conjugate have inverse classes, so one of each pair
\\ is listed. Class groups use bnfinit under GRH (statistics only).
\\ output line: x h cyc [d_1, ..., d_r]  (r = 2^(omega-1) - 1 mixed pairs)
\\ usage: (echo 'X0=3; X1=100001;'; cat analysis/r3nt_mixed_orders.gp) | gp -q
default(parisizemax, 10^9);
classorder(K, I) = {
  my(v = bnfisprincipal(K, I, 0), c = K.cyc, d = 1);
  for (i = 1, #c, d = lcm(d, c[i] / gcd(c[i], v[i])));
  d;
}
{
forstep (x = X0 + (X0 % 2 == 0), X1, 2,
  my(fa = factor(x), np = #fa~);
  if (np < 2 || issquare(x), next);
  my(D = x^2 + 4, K = bnfinit(w^2 - D, 1), P, prs = vector(np), cps = vector(np), ds = List());
  P = idealhnf(K, w/2 + x/2 + 1);
  for (i = 1, np,
    my(pr = idealprimedec(K, fa[i, 1]));
    if (idealval(K, P, pr[1]) > 0, prs[i] = pr[1]; cps[i] = pr[2], prs[i] = pr[2]; cps[i] = pr[1]));
  \\ masks with the top bit clear pick one of each conjugate pair; mask 0 is P'
  for (mask = 1, 2^(np - 1) - 1,
    my(B = 1);
    for (i = 1, np, B = idealmul(K, B, idealpow(K, if (bittest(mask, i - 1), prs[i], cps[i]), fa[i, 2])));
    listput(ds, classorder(K, B)));
  print(x, " ", K.no, " ", K.cyc, " ", Vec(ds)));
}
\q
