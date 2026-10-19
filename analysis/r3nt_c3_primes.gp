\\ Question 51, section 4.3: for primes x == +-1 (mod 12), the order d of the
\\ class of a prime above x in Q(sqrt(x^2 + 12)) (maximal order, GRH), and
\\ how often a principal prime comes with a regulator above the bound of
\\ Proposition 4.10, sqrt(x log x) / (21 M), M = max(log(2x) + 0.38, 5).
\\ usage: (echo 'X=20000;'; cat analysis/r3nt_c3_primes.gp) | gp -q
default(parisizemax, 10^9);
{
my(np = 0, nprinc = 0, nbig = 0, dmax = 0, nord = 0, rat = List());
forprime (x = 5, X,
  if (x % 12 != 1 && x % 12 != 11, next);
  np++;
  my(K = bnfinit(w^2 - (x^2 + 12), 1), pr = idealprimedec(K, x)[1], v, d = 1, mu0 = K.reg, M);
  v = bnfisprincipal(K, pr, 0);
  for (i = 1, #K.cyc, d = lcm(d, K.cyc[i] / gcd(K.cyc[i], v[i])));
  if (d == x, nord++);
  if (d == 1,
    nprinc++;
    M = max(log(2*x) + 0.38, 5);
    if (mu0 > sqrt(x*log(x))/(21*M), nbig++);
    listput(rat, mu0 / sqrt(x)));
  dmax = max(dmax, d));
my(r = vecsort(Vec(rat)));
print(np, " primes x == +-1 (mod 12) in [5, ", X, "]; class of a prime above x principal for ", nprinc,
      "; of these, regulator above the bound of Proposition 4.10: ", nbig,
      "; class of order x: ", nord, "; largest order: ", dmax);
print("regulator / sqrt(x) for the principal cases: median ", r[#r \ 2], ", 10% quantile ", r[#r \ 10], ", 90% quantile ", r[9 * #r \ 10]);
}
\q
