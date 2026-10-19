/* Round 6, basics: sieve the families (p, q, x) and (p, x, q) over even x.

   For a family with fixed digits p >= 1, q >= 0 and an even large digit x,
   the string is a solution in base b exactly when D is a perfect square,
   D = (2pb + q)^2 (last) or (2pb + x)^2 (middle), where

     last:   D = q^2 + 4p (w(p) + w(q) + x^x - x)
     middle: D = x^2 + 4p (w(p) + w(q) + x^x - q)

   and w(0) = m, the convention. The program tests D modulo odd primes:
   a non-square residue excludes x. x^x mod l depends on x mod l(l-1), so
   each prime has a table of that period. The first five primes form a wheel
   of period 60060.

   input lines: p q pos m X0    (pos is "last" or "mid")
   output: one line per family with the count of even x in [2, X0] tested,
   then "survivor p q pos m x" for each x that passes every prime.

   With the argument "sq" the program tests the odd squares x = t^2 instead,
   for odd t <= X0, with a wheel on t (t^2 mod L depends on t mod L).

   build: gcc -O3 -march=native -fopenmp -o r6b_sieve r6b_sieve.c
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

/* w(d) mod l for a fixed digit d >= 0 */
static uint64_t wmod(uint64_t d, int m, uint64_t l) {
    if (d == 0) return m % l;
    return powmod(d, d, l);
}

int main(int argc, char **argv) {
    int sq = argc > 1 && strcmp(argv[1], "sq") == 0;
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
    uint64_t p, q, X0;
    char pos[8];
    int m;
    uint8_t *wheel = malloc(WHEEL);
    uint8_t *tab[NP];
    for (int i = 0; i < NP; i++) tab[i] = malloc((uint64_t)P[i] * (P[i] - 1));
    while (scanf("%lu %lu %7s %d %lu", &p, &q, pos, &m, &X0) == 5) {
        int mid = strcmp(pos, "mid") == 0;
        #pragma omp parallel for schedule(dynamic, 1)
        for (int i = 0; i < NP; i++) {
            uint64_t l = P[i], L = l * (l - 1);
            uint64_t wp = wmod(p, m, l), wq = wmod(q, m, l), pl = p % l, ql = q % l;
            /* pw[a (l-1) + e] = a^e mod l */
            uint32_t *pw = malloc(l * (l - 1) * sizeof *pw);
            for (uint64_t a = 0; a < l; a++) {
                uint64_t v = 1;
                for (uint64_t e = 0; e < l - 1; e++) {
                    pw[a * (l - 1) + e] = v;
                    v = v * a % l;
                }
            }
            for (uint64_t r = 0; r < L; r++) {
                uint64_t a = r % l;
                uint64_t xx = a == 0 ? 0 : pw[a * (l - 1) + r % (l - 1)];
                uint64_t c = (wp + wq + xx) % l, d;
                if (mid) d = (a * a + 4 * pl * ((c + l - ql) % l)) % l;
                else d = (ql * ql + 4 * pl * ((c + l - a) % l)) % l;
                tab[i][r] = qr[i][d];
            }
            free(pw);
        }
        /* x + L has the same residue as x, and r + L avoids x = 0 */
        for (uint64_t r = 0; r < WHEEL; r++) {
            uint8_t ok = 1;
            for (int i = 0; i < NW; i++) {
                uint64_t L = (uint64_t)P[i] * (P[i] - 1);
                ok &= tab[i][(sq ? r * r : r) % L];
            }
            wheel[r] = ok;
        }
        uint64_t tested = 0;
        #pragma omp parallel for schedule(dynamic, 1) reduction(+:tested)
        for (uint64_t blk = 0; blk <= X0 / WHEEL; blk++) {
            uint64_t base = blk * WHEEL;
            for (uint64_t r = sq; r < WHEEL; r += 2) {
                uint64_t t = base + r, x = sq ? t * t : t;
                if (t < 2 - sq || t > X0) continue;
                tested++;
                if (!wheel[r]) continue;
                int i;
                for (i = NW; i < NP; i++) {
                    uint64_t L = (uint64_t)P[i] * (P[i] - 1);
                    if (!tab[i][x % L]) break;
                }
                if (i == NP) {
                    #pragma omp critical
                    printf("survivor %lu %lu %s %d %lu\n", p, q, pos, m, x);
                }
            }
        }
        printf("family %lu %lu %s %d X0 %lu tested %lu\n", p, q, pos, m, X0, tested);
        fflush(stdout);
    }
    return 0;
}
