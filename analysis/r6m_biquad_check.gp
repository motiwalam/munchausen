\\ Chapter 38, Lemma 38.4: in M = Q(sqrt R, sqrt(pA)), R = x^2 + 4pA,
\\ pA not a square, x an odd prime with (pA/x) = 1, the x-part of
\\ z = (theta + k)/(theta - k) is (I^-1 tau(I)) and L/L' = I tau(I).
\\ Prints the support of z away from x and checks both identities.
\\ usage: gp -q r6m_biquad_check.gp
chk(c, X)={
  my(R = X^2 + 4*c, P = subst(polcompositum('t^2 - R, 't^2 - c)[1], 't, 'y), nf = nfinit(P));
  my(r1 = nfroots(nf, 'x^2 - R), r2 = nfroots(nf, 'x^2 - c));
  my(sR = r1[1], k = r2[1], th = (X + sR)/2);
  my(z = nfeltdiv(nf, th + k, th - k));
  my(pr = idealprimedec(nf, X), L1 = 0);
  \\ L1: a prime above x with theta == k
  for(i = 1, #pr, if(nfeltval(nf, th - k, pr[i]) > 0, L1 = pr[i]; break));
  \\ automorphisms: sigma fixes k, sends sR -> -sR; tau fixes sR, k -> -k
  my(G = nfgaloisconj(nf), sg = 0, ta = 0);
  for(j = 1, #G, my(a = nfgaloisapply(nf, G[j], sR), b = nfgaloisapply(nf, G[j], k));
    if(a == -sR && b == k, sg = G[j]); if(a == sR && b == -k, ta = G[j]));
  if(sg == 0 || ta == 0 || L1 == 0, print([c, X, "automorphisms or L1 not found, skipped"]); return);
  my(sL1 = nfgaloisapply(nf, sg, L1), tL1 = nfgaloisapply(nf, ta, L1));
  my(stL1 = nfgaloisapply(nf, sg, tL1));
  my(I = idealdiv(nf, L1, sL1), tI = idealdiv(nf, tL1, stL1));
  my(fz = idealfactor(nf, z), xpart = 1, other = []);
  for(i = 1, #fz~, if(fz[i,1].p == X, xpart = idealmul(nf, xpart, idealpow(nf, fz[i,1], fz[i,2])),
                    other = concat(other, [[fz[i,1].p, fz[i,2]]])));
  my(ok1 = (xpart == idealdiv(nf, tI, I)) || (xpart == idealdiv(nf, I, tI)));
  my(Lmu = idealmul(nf, L1, tL1), Lp = nfgaloisapply(nf, sg, Lmu));
  my(ok2 = idealdiv(nf, Lmu, Lp) == idealmul(nf, I, tI));
  print([c, X, "x-part of z = I^-1 tau(I) (up to inversion):", ok1,
         "L/L' = I tau(I):", ok2, "other support of z (p, e):", other]);
};
\\ p A = c not a square; x prime with (c/x) = 1
{ forstep(c = 2, 30, 1, if(issquare(c), next);
    my(n = 0); forprime(xx = 3, 200, if(gcd(xx, 2*c) > 1 || kronecker(c, xx) != 1, next);
      if(issquare(xx^2 + 4*c), next);
      chk(c, xx); n++; if(n >= 2, break))) };
