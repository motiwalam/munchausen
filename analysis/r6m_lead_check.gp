\\ Round 6 middle draft: Lemma M.5 on artificial equations
\\ U^2 = 4 x^n + R, R = q^2 + 4xA, U = 2xb + q, x even.
\\ Claim: mu / theta^n is an S-unit, S = primes above A*q (n large enough).
\\ usage: gp -q r6m_lead_check.gp
cnt=0; bad=0;
{for(x=2,3000, if(x%2,next);
 for(q=1,7, for(A=1,60, my(R=q^2+4*x*A); if(issquare(R),next);
  for(n=3,9, my(D=4*x^n+R, U); if(!issquare(D,&U),next);
   if((U-q)%(2*x),next); my(b=(U-q)/(2*x)); if(b<=0,next);
   my(P=y^2-R, nf=nfinit(P), th=Mod((q+y)/2,P), mu=Mod((U+y)/2,P));
   my(nu=lift(mu/th^n), id=idealfactor(nf,nu), okS=1);
   for(i=1,#id~, my(l=id[i,1].p); if((A*q)%l, okS=0));
   cnt++; if(!okS, bad++; print("FAIL ",[x,q,A,n,b,id[,1]~]));
   if(cnt<=12, print([x,q,A,n,b,"support of nu:",vector(#id~,i,id[i,1].p)]))))))};
print("tested ",cnt," failures ",bad);
