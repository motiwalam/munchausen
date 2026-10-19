\\ Question 52, Lemma 3.2: for x == 0 mod 8 and E = (x/2)^2 + 1 squarefree, the
\\ order t of the class of a prime Q above 2 in Q(sqrt E) is at least
\\ floor(log2 x) - 2. Also lists t for the first x.
\\ usage: (echo 'X=4000;'; cat analysis/r3nt_even_q.gp) | gp -q
default(parisizemax, 10^9);
{
my(bad = 0, cnt = 0, minsl = 10^9, out = List());
forstep (x = 8, X, 8,
  my(E = (x/2)^2 + 1, K, Q, t, lb);
  if (!issquarefree(E), next);
  cnt++;
  K = bnfinit(y^2 - E, 1);
  Q = idealprimedec(K, 2)[1];
  t = 1; while (bnfisprincipal(K, idealpow(K, Q, t), 0) != 0, t++);
  lb = logint(x, 2) - 2;
  if (t < lb, bad++; print("FAIL x = ", x, " t = ", t));
  minsl = min(minsl, t - lb);
  if (#out < 12, listput(out, [x, t, lb])));
print(cnt, " values x == 0 mod 8 up to ", X, " with E squarefree; failures of t >= floor(log2 x) - 2: ", bad,
      "; smallest t - (floor(log2 x) - 2): ", minsl);
print("first [x, t, bound]: ", out);
}
\q
