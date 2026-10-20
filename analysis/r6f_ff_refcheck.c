/* Chapter 36, referee check of r6f_ff_sieve.c by a different method.

   For a 3-digit string with small digits a, c and a large digit x, the
   string is a solution exactly when V is a perfect square, where
     pos 0, last (a, c, x):  V = c^2 + 4a (w(a) + w(c) + x^x - x)
     pos 1, mid  (a, x, c):  V = x^2 + 4a (w(a) + w(c) + x^x - c)
     pos 2, lead (x, a, c):  V = a^2 + 4x (x^x + w(a) + w(c) - c)
   This program tests V modulo the 48 largest primes below 2^32 by Euler's
   criterion, with x^x mod l computed by a direct modular power (no period
   tables, no wheel, primes disjoint from those of r6f_ff_sieve.c).

   input lines: pos a c m x0 x1 par   (m = w(0), par = parity of x)
   output: "survivor pos a c m x", then one "family" line per input line.
   inputs: r6f_ff_refexact.py inputs last | midlead
   build: gcc -O3 -march=native -fopenmp -o r6f_ff_refcheck r6f_ff_refcheck.c
*/
#include <stdio.h>
#include <stdint.h>
#define NP 48
static uint64_t P[NP];
static uint64_t pm(uint64_t a, uint64_t e, uint64_t m){uint64_t r=1%m;a%=m;while(e){if(e&1)r=r*a%m;a=a*a%m;e>>=1;}return r;}
static int isprime(uint64_t n){for(uint64_t d=2;d*d<=n;d++)if(n%d==0)return 0;return 1;}
static uint64_t wm(uint64_t d,int m,uint64_t l){return d==0?(uint64_t)m%l:pm(d,d,l);}
int main(void){
  int k=0; for(uint64_t c=4294967291ULL;k<NP;c-=2) if(isprime(c)) P[k++]=c;
  uint64_t a,c,x0,x1,par; int m,pos;
  while(scanf("%d %lu %lu %d %lu %lu %lu",&pos,&a,&c,&m,&x0,&x1,&par)==7){
    if(x0%2!=par) x0++;
    uint64_t tested=0,surv=0;
    #pragma omp parallel for schedule(dynamic,1) reduction(+:tested,surv)
    for(uint64_t blk=x0; blk<=x1; blk+=200000){
      uint64_t end = blk+200000-1 < x1 ? blk+200000-1 : x1;
      for(uint64_t x=blk; x<=end; x+=2){
        tested++; int ok=1;
        for(int i=0;i<NP;i++){uint64_t l=P[i];
          uint64_t xx=pm(x,x,l), wa=wm(a,m,l), wc=wm(c,m,l), al=a%l, cl=c%l, xl=x%l, v;
          if(pos==0){uint64_t s=(wa+wc+xx+l-xl)%l; v=(cl*cl%l + (4*al)%l*s)%l;}
          else if(pos==1){uint64_t s=(wa+wc+xx+l-cl)%l; v=(xl*xl%l + (4*al)%l*s)%l;}
          else {uint64_t s=(xx+wa+wc+l-cl)%l; v=(al*al%l + (4*xl)%l*s)%l;}
          if(v==0) continue;
          if(pm(v,(l-1)/2,l)!=1){ok=0;break;}
        }
        if(ok){surv++;
          #pragma omp critical
          printf("survivor %d %lu %lu %d %lu\n",pos,a,c,m,x);}
      }
    }
    printf("family %d %lu %lu %d %lu..%lu par %lu tested %lu survivors %lu\n",pos,a,c,m,x0,x1,par,tested,surv);
    fflush(stdout);
  }
  return 0;
}
