/* Referee sieve for chapter 38: different primes (40 primes just above 2^31)
   and direct arithmetic: D mod l computed with modular powers, squareness
   by Euler's criterion. Families:
     mid  (a, x, c): D = x^2 + 4a (w(a) + w(c) + x^x - c)
     lead (x, a, c): D = a^2 + 4x (x^x + w(a) + w(c) - c)
   input: a c pos m x0 x1 par ; prints survivors and counts. */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#define NP 40
static uint64_t P[NP];
static uint64_t pm(uint64_t a, uint64_t e, uint64_t m){uint64_t r=1%m;a%=m;while(e){if(e&1)r=r*a%m;a=a*a%m;e>>=1;}return r;}
static int isprime(uint64_t n){if(n<2)return 0;for(uint64_t d=2;d*d<=n;d++)if(n%d==0)return 0;return 1;}
static uint64_t wm(uint64_t d,int m,uint64_t l){return d==0? (uint64_t)m%l : pm(d,d,l);}
int main(void){
  int n=0; for(uint64_t c=(1ULL<<31)+1; n<NP; c+=2) if(isprime(c)) P[n++]=c;
  uint64_t a,c,x0,x1; char pos[8]; int m,par;
  while(scanf("%lu %lu %7s %d %lu %lu %d",&a,&c,pos,&m,&x0,&x1,&par)==7){
    int lead = strcmp(pos,"lead")==0;
    uint64_t wa[NP], wc[NP];
    for(int i=0;i<NP;i++){wa[i]=wm(a,m,P[i]); wc[i]=wm(c,m,P[i]);}
    uint64_t start = x0 + ((x0 & 1) != (uint64_t)par);
    uint64_t tested=0, surv=0;
    #pragma omp parallel for schedule(dynamic,4096) reduction(+:tested,surv)
    for(uint64_t x=start; x<=x1; x+=2){
      tested++;
      int i;
      for(i=0;i<NP;i++){
        uint64_t l=P[i], xl=x%l;
        uint64_t xx = xl==0?0:pm(xl, x%(l-1), l);   /* x^x mod l, Fermat */
        uint64_t D;
        if(lead){ uint64_t s=(xx+wa[i]+wc[i]+l-(c%l))%l; D=((a%l)*(a%l)%l + 4*xl%l*s)%l; }
        else    { uint64_t s=(wa[i]+wc[i]+xx+l-(c%l))%l; D=(xl*xl%l + (4*(a%l))%l*s)%l; }
        if(D!=0 && pm(D,(l-1)/2,l)!=1) break;
      }
      if(i==NP){ surv++;
        #pragma omp critical
        printf("survivor %lu %lu %s %d %lu\n",a,c,pos,m,x);}
    }
    printf("family %lu %lu %s %d x %lu..%lu par %d tested %lu survivors %lu\n",a,c,pos,m,x0,x1,par,tested,surv);
    fflush(stdout);
  }
  return 0;
}
