\\ Round 6 middle draft: regulators of Q(sqrt(x^2 + 4k^2)) for odd primes x
\\ (exact, quadregulator). How often is Reg at most 2k + log x + 1?
\\ usage: gp -q r6m_regulators.gp
reg(k,X0,cnt)={my(n=0,small=0,s=0.,mn=10^9,mx=0.);
 forprime(x=X0,oo, if(gcd(x,2*k)>1,next); my(R=x^2+4*k^2, D=coredisc(R), r=quadregulator(D));
  n++; s+=r/x; mn=min(mn,r/x); mx=max(mx,r/x); if(r<=2*k+log(x)+1, small++); if(n>=cnt,break));
 printf("k=%d x>%d n=%d mean Reg/x=%.4f min %.5f max %.4f  #Reg<=2k+log x+1: %d\n",k,X0,n,s/n,mn,mx,small)};
reg(5,10^5,2000);
reg(5,10^7,500);
reg(9,10^5,2000);
reg(1,10^5,2000);
