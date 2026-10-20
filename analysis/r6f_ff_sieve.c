/* Round 6, field families: sieve 3-digit strings with one large digit x
   of either parity in a range [x0, x1].

   For fixed small digits the string is a solution in base b exactly when
   D is a perfect square, where (w(0) = m, w(d) = d^d)

     last  (a, c, x):  D = c^2 + 4a (w(a) + w(c) + x^x - x)
     mid   (a, x, c):  D = x^2 + 4a (w(a) + w(c) + x^x - c)
     lead  (x, a, c):  D = a^2 + 4x (x^x + w(a) + w(c) - c)

   D = (2ab + c)^2, (2ab + x)^2 or (2xb + a)^2. The program tests D modulo
   150 odd primes; D mod l depends on x mod l(l-1). The first five primes
   form a wheel of period 60060. This extends r6b_sieve.c (even x, last and
   middle only) to odd x and to the leading position.

   input lines: a c pos m x0 x1 par   (pos is last, mid or lead; par is the
   parity of x: 0 even, 1 odd)
   output: "survivor a c pos m x" for each x that passes every prime, then
   one line per family with the number of x tested.

   build: gcc -O3 -march=native -fopenmp -o r6f_ff_sieve r6f_ff_sieve.c
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define NP 150
#define NW 5
#define WHEEL 60060
static uint32_t P[NP];

static uint64_t powmod(uint64_t a, uint64_t e, uint64_t m) {
    uint64_t r = 1 % m;
    a %= m;
    while (e) {
        if (e & 1) r = r * a % m;
        a = a * a % m;
        e >>= 1;
    }
    return r;
}

static uint64_t wmod(uint64_t d, int m, uint64_t l) {
    if (d == 0) return m % l;
    return powmod(d, d, l);
}

int main(void) {
    int n = 0;
    for (uint32_t c = 3; n < NP; c += 2) {
        int pr = 1;
        for (uint32_t d = 3; d * d <= c; d += 2)
            if (c % d == 0) { pr = 0; break; }
        if (pr) P[n++] = c;
    }
    uint8_t *qr[NP];
    for (int i = 0; i < NP; i++) {
        qr[i] = calloc(P[i], 1);
        for (uint64_t a = 0; a < P[i]; a++) qr[i][a * a % P[i]] = 1;
    }
    uint64_t a, c, x0, x1;
    char pos[8];
    int m, par;
    uint8_t *wheel = malloc(WHEEL);
    uint8_t *tab[NP];
    for (int i = 0; i < NP; i++) tab[i] = malloc((uint64_t)P[i] * (P[i] - 1));
    while (scanf("%lu %lu %7s %d %lu %lu %d", &a, &c, pos, &m, &x0, &x1, &par) == 7) {
        int kind = strcmp(pos, "last") == 0 ? 0 : strcmp(pos, "mid") == 0 ? 1 : 2;
        #pragma omp parallel for schedule(dynamic, 1)
        for (int i = 0; i < NP; i++) {
            uint64_t l = P[i], L = l * (l - 1);
            uint64_t wa = wmod(a, m, l), wc = wmod(c, m, l), al = a % l, cl = c % l;
            uint32_t *pw = malloc(l * (l - 1) * sizeof *pw);
            for (uint64_t u = 0; u < l; u++) {
                uint64_t v = 1;
                for (uint64_t e = 0; e < l - 1; e++) {
                    pw[u * (l - 1) + e] = v;
                    v = v * u % l;
                }
            }
            for (uint64_t r = 0; r < L; r++) {
                uint64_t xl = r % l;
                uint64_t xx = xl == 0 ? 0 : pw[xl * (l - 1) + r % (l - 1)];
                uint64_t d;
                if (kind == 0) {
                    uint64_t s = (wa + wc + xx + l - xl) % l;
                    d = (cl * cl + 4 * al % l * s) % l;
                } else if (kind == 1) {
                    uint64_t s = (wa + wc + xx + l - cl) % l;
                    d = (xl * xl + 4 * al % l * s) % l;
                } else {
                    uint64_t s = (xx + wa + wc + l - cl) % l;
                    d = (al * al + 4 * xl % l * s) % l;
                }
                tab[i][r] = qr[i][d];
            }
            free(pw);
        }
        for (uint64_t r = 0; r < WHEEL; r++) {
            uint8_t ok = 1;
            for (int i = 0; i < NW; i++) {
                uint64_t L = (uint64_t)P[i] * (P[i] - 1);
                ok &= tab[i][r % L];
            }
            wheel[r] = ok;
        }
        uint64_t tested = 0;
        #pragma omp parallel for schedule(dynamic, 1) reduction(+:tested)
        for (uint64_t blk = x0 / WHEEL; blk <= x1 / WHEEL; blk++) {
            uint64_t base = blk * WHEEL;
            for (uint64_t r = par; r < WHEEL; r += 2) {
                uint64_t x = base + r;
                if (x < x0 || x > x1) continue;
                tested++;
                if (!wheel[r]) continue;
                int i;
                for (i = NW; i < NP; i++) {
                    uint64_t L = (uint64_t)P[i] * (P[i] - 1);
                    if (!tab[i][x % L]) break;
                }
                if (i == NP) {
                    #pragma omp critical
                    printf("survivor %lu %lu %s %d %lu\n", a, c, pos, m, x);
                }
            }
        }
        printf("family %lu %lu %s %d x %lu..%lu par %d tested %lu\n", a, c, pos, m, x0, x1, par, tested);
        fflush(stdout);
    }
    return 0;
}
