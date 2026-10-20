\\ Round 6, k-length: the size of the field of P_x - W for 4 digits
\\ (Table K.5.1). For a 4-digit string with one large digit x, a solution
\\ says P_x(b) - W = x^x, and the factorization of the left side lives in
\\ the cubic field K_x of P_x(r) - W. The script samples x and prints the
\\ means of |D_K| / x^2, h R / x and h R / sqrt|D_K|, with bnfinit (so h R
\\ is under GRH; illustration only).
\\
\\ usage: gp -q r6k_fields.gp

default(parisize, 10^9);
W(d, m) = if(d == 0, m, d^d);

\\ the cubic P_x(r) - W for digits s (x at index ix, 1-based), convention m
cub(s, ix, m, x) = {
  my(Wt = sum(i = 1, 4, if(i == ix, 0, W(s[i], m))), c = s);
  c[ix] = x;
  c[1] * r^3 + c[2] * r^2 + c[3] * r + c[4] - Wt;
}

sample(name, s, ix, m, X, n, cong) = {
  my(sD = 0., shR = 0., sq = 0., cnt = 0, x = X);
  while(cnt < n,
    x++;
    if(x % cong[2] != cong[1], next);
    my(f = cub(s, ix, m, x), g, bnf, D);
    if(!polisirreducible(f), next);
    g = polredbest(f);
    bnf = bnfinit(g, 1);
    D = abs(bnf.disc);
    sD += D / x^2; shR += bnf.no * bnf.reg / x; sq += bnf.no * bnf.reg / sqrt(D);
    cnt++);
  printf("%-34s X = %.0e  n = %d  mean |D|/x^2 = %.3f  mean hR/x = %.4f  mean hR/sqrt|D| = %.4f\n",
         name, X, n, sD / n, shR / n, sq / n);
}

{
  foreach([10^4, 10^6], X,
    sample("last (1,1,1,x)", [1,1,1,0], 4, 1, X, 40, [0, 1]);
    sample("last (1,2,3,x)", [1,2,3,0], 4, 1, X, 40, [0, 1]);
    sample("last (2,0,0,x), x = 1 mod 3", [2,0,0,0], 4, 1, X, 40, [1, 3]);
    sample("middle (1,x,1,1)", [1,0,1,1], 2, 1, X, 40, [0, 1]);
    sample("middle (1,1,x,1)", [1,1,0,1], 3, 1, X, 40, [0, 1]);
    sample("leading (x,1,1,1)", [0,1,1,1], 1, 1, X, 40, [0, 1]);
    sample("leading (x,1,2,0)", [0,1,2,0], 1, 1, X, 40, [0, 1]));
}
quit;
