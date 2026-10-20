\\ Chapter 38: Lemma 38.1 and Theorem 38.2 on artificial equations
\\ p b^2 + x b - A = x^n with pA = k^2 and small n. For each solution with x
\\ prime to 2k it looks for e, a, s with (mu/mu')^e z^(-s e n) (theta/k)^(-a)
\\ a unit and prints k^a Tr(w). Prime powers x must always have one.
\\ usage: gp -q r6m_square_check.gp
test(p,A,k,X,N)={my(cnt=0,bad=0);
 for(x=3,X, if(x%2==0 || gcd(x,2*k)!=1, next);
  for(n=2,N, my(D=x^2+4*p*(x^n+A), U); if(!issquare(D,&U), next);
   if((U-x)%(2*p), next); my(b=(U-x)/(2*p)); if(b<=0,next);
   my(R=x^2+4*k^2); if(issquare(R), next);
   my(P=y^2-R, nf=nfinit(P), th=Mod((x+y)/2,P), z=(th+k)/(th-k), mu=Mod((U+y)/2,P));
   my(mup=Mod((U-y)/2,P));
   my(ok=0);
   for(e=1,12, for(a=0,12, for(s=-1,1, if(s==0,next);
     my(w=(mu/mup)^e*z^(-s*e*n)*(th/k)^(-a));
     my(id=idealhnf(nf,lift(w)));
     if(id==matid(2), ok=[e,a,s]; break(3)))));
   if(ok, cnt++; my(e=ok[1],a=ok[2],s=ok[3], w=(mu/mup)^e*z^(-s*e*n), tr=trace(w)*k^a);
     print([p,A,k,x,n,b,"e,a,s=",ok,"k^a*tr=",tr, "omega(x)=",omega(x)]),
     bad++; print("NO UNIT ", [p,A,k,x,n,b,omega(x)]))));
 print("found ",cnt," without ",bad)};
test(1,1,1,400,9);
test(1,25,5,3000,5);
test(3,27,9,2000,4);
test(1,4,2,2000,5);
test(1,9,3,3000,5);
test(3,3,3,3000,5);
test(5,125,25,2000,4);
