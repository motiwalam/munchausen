/* Round 5, families: sieve for 3-digit solutions under 0^0 = 1.

   A string (p, q, r), p >= 1, is a solution in base b exactly when
   D = 4p (w(p) + w(q) + w(r) - r) + q^2 is a perfect square s^2 and
   b = (s - q) / (2p) is an integer above every digit. This program prints
   every string of the chosen ranges for which D is a square modulo all odd
   primes below 600 (108 primes). r5f_sieve3.py checks the survivors exactly.

   usage: r5f_sieve3 last  P Q R   strings (p, q, r), 1 <= p <= P, q <= Q, r <= R
          r5f_sieve3 mid   P X R   strings (p, x, r), 1 <= p <= P, x <= X, r <= R
          r5f_sieve3 lead  X Q R   strings (x, q, r), 1 <= x <= X, q <= Q, r <= R
   The large digit runs in the innermost loop.

   build: gcc -O3 -march=native -o r5f_sieve3 r5f_sieve3.c
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define NP 108
static uint32_t P[NP];
static uint8_t *QR[NP];      /* QR[i][a] = 1 if a is a square mod P[i] */
static uint16_t *WM[NP];     /* w(d) mod P[i] */
static uint16_t *GM[NP];     /* w(d) - d mod P[i] */
static uint16_t *SQ[NP];     /* d^2 mod P[i] */
static uint16_t *A4W[NP];    /* 4 d w(d) mod P[i] */
static uint16_t *F4[NP];     /* 4 d mod P[i] */

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

static void setup(long N) {
    int n = 0;
    for (uint32_t c = 3; n < NP; c += 2) {
        int pr = 1;
        for (uint32_t d = 3; d * d <= c; d += 2)
            if (c % d == 0) { pr = 0; break; }
        if (pr) P[n++] = c;
    }
    for (int i = 0; i < NP; i++) {
        uint32_t l = P[i];
        QR[i] = calloc(l, 1);
        for (uint32_t a = 0; a < l; a++) QR[i][(uint64_t)a * a % l] = 1;
        WM[i] = malloc((N + 1) * 2);
        GM[i] = malloc((N + 1) * 2);
        SQ[i] = malloc((N + 1) * 2);
        A4W[i] = malloc((N + 1) * 2);
        F4[i] = malloc((N + 1) * 2);
        for (long d = 0; d <= N; d++) {
            uint64_t wd = d == 0 ? 1 : powmod(d, d, l);
            WM[i][d] = wd;
            GM[i][d] = (wd + l - d % l) % l;
            SQ[i][d] = (uint64_t)(d % l) * (d % l) % l;
            A4W[i][d] = 4 * (uint64_t)(d % l) % l * wd % l;
            F4[i][d] = 4 * (uint64_t)(d % l) % l;
        }
    }
    if (P[NP - 1] >= 65536) { fprintf(stderr, "prime too large\n"); exit(1); }
}

static uint32_t K[NP], A[NP], C2[NP];

int main(int argc, char **argv) {
    if (argc != 5) { fprintf(stderr, "usage: r5f_sieve3 last|mid|lead n1 n2 n3\n"); return 1; }
    const char *mode = argv[1];
    long n1 = atol(argv[2]), n2 = atol(argv[3]), n3 = atol(argv[4]);
    long N = n1 > n2 ? n1 : n2;
    if (n3 > N) N = n3;
    setup(N);
    long long tested = 0, surv = 0;
    if (!strcmp(mode, "last")) {
        /* (p, q, r): D = 4p(w(p) + w(q)) + q^2 + 4p g(r); inner loop over r */
        for (long p = 1; p <= n1; p++)
            for (long q = 0; q <= n2; q++) {
                for (int i = 0; i < NP; i++) {
                    uint64_t l = P[i];
                    K[i] = (F4[i][p] * (uint64_t)((WM[i][p] + WM[i][q]) % l) + SQ[i][q]) % l;
                    A[i] = F4[i][p];
                }
                for (long r = 0; r <= n3; r++) {
                    int i;
                    for (i = 0; i < NP; i++)
                        if (!QR[i][(K[i] + A[i] * (uint32_t)GM[i][r]) % P[i]]) break;
                    if (i == NP) { printf("%ld %ld %ld\n", p, q, r); surv++; }
                }
                tested += n3 + 1;
            }
    } else if (!strcmp(mode, "mid")) {
        /* (p, x, r): D = 4p(w(p) + g(r)) + 4p w(x) + x^2; inner loop over x */
        for (long p = 1; p <= n1; p++)
            for (long r = 0; r <= n3; r++) {
                for (int i = 0; i < NP; i++) {
                    uint64_t l = P[i];
                    K[i] = F4[i][p] * (uint64_t)((WM[i][p] + GM[i][r]) % l) % l;
                    A[i] = F4[i][p];
                }
                for (long x = 0; x <= n2; x++) {
                    int i;
                    for (i = 0; i < NP; i++)
                        if (!QR[i][(K[i] + A[i] * (uint32_t)WM[i][x] + SQ[i][x]) % P[i]]) break;
                    if (i == NP) { printf("%ld %ld %ld\n", p, x, r); surv++; }
                }
                tested += n2 + 1;
            }
    } else if (!strcmp(mode, "lead")) {
        /* (x, q, r): D = 4x w(x) + 4x (w(q) + g(r)) + q^2; inner loop over x */
        for (long q = 0; q <= n2; q++)
            for (long r = 0; r <= n3; r++) {
                for (int i = 0; i < NP; i++) {
                    uint64_t l = P[i];
                    K[i] = (WM[i][q] + GM[i][r]) % l;
                    C2[i] = SQ[i][q];
                }
                for (long x = 1; x <= n1; x++) {
                    int i;
                    for (i = 0; i < NP; i++)
                        if (!QR[i][(A4W[i][x] + F4[i][x] * K[i] + C2[i]) % P[i]]) break;
                    if (i == NP) { printf("%ld %ld %ld\n", x, q, r); surv++; }
                }
                tested += n1;
            }
    } else {
        fprintf(stderr, "unknown mode %s\n", mode);
        return 1;
    }
    fprintf(stderr, "# mode %s %ld %ld %ld: %lld strings, %lld survivors\n", mode, n1, n2, n3, tested, surv);
    return 0;
}
