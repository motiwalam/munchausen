/* Round 6, k-length, referee: a second sieve for the k-digit families of
   r6k_sieve.c, written separately. For each x it reduces the equation
   Ps(b) + x b^j - W - x^x = 0 modulo NP primes just above 2^31 (no tables,
   direct modular powers) and tests for a root by gcd(f, b^l - b) over F_l.
   A string that is a solution survives every prime.

   input lines:  k j m x0 x1 M a d_1 ... d_(k-1)   (as r6k_sieve.c)
   output: survivors and one line per family.

   build: gcc -O2 -fopenmp -o r6k_refsieve r6k_refsieve.c
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#define NP 40
#define KMAX 16
typedef unsigned __int128 u128;
static uint64_t P[NP];

static uint64_t mulm(uint64_t a, uint64_t b, uint64_t m) { return (u128)a * b % m; }
static uint64_t powm(uint64_t a, uint64_t e, uint64_t m) {
    uint64_t r = 1 % m; a %= m;
    while (e) { if (e & 1) r = mulm(r, a, m); a = mulm(a, a, m); e >>= 1; }
    return r;
}
static int isprime(uint64_t n) {
    if (n < 2) return 0;
    for (uint64_t d = 2; d * d <= n; d++) if (n % d == 0) return 0;
    return 1;
}

/* polynomials over F_l: c[0..deg], c[deg] != 0; deg = -1 for zero */
typedef struct { int deg; uint64_t c[2 * KMAX]; } poly;

static void trim(poly *f) { while (f->deg >= 0 && f->c[f->deg] == 0) f->deg--; }

static void pmod(poly *a, const poly *f, uint64_t l) {   /* a %= f, f monic */
    if (a->deg < f->deg) return;
    for (int i = a->deg; i >= f->deg; i--) {
        uint64_t t = a->c[i];
        if (!t) continue;
        for (int u = 0; u <= f->deg; u++)
            a->c[i - f->deg + u] = (a->c[i - f->deg + u] + l - mulm(t, f->c[u], l)) % l;
    }
    a->deg = f->deg - 1;
    trim(a);
}

static void pmulmod(poly *r, const poly *a, const poly *b, const poly *f, uint64_t l) {
    poly t; t.deg = (a->deg < 0 || b->deg < 0) ? -1 : a->deg + b->deg;
    for (int i = 0; i <= t.deg; i++) t.c[i] = 0;
    for (int i = 0; i <= a->deg; i++)
        for (int j = 0; j <= b->deg; j++)
            t.c[i + j] = (t.c[i + j] + mulm(a->c[i], b->c[j], l)) % l;
    trim(&t);
    pmod(&t, f, l);
    *r = t;
}

static void monic(poly *f, uint64_t l) {
    uint64_t inv = powm(f->c[f->deg], l - 2, l);
    for (int i = 0; i <= f->deg; i++) f->c[i] = mulm(f->c[i], inv, l);
}

/* does f have a root in F_l? */
static int hasroot(poly f, uint64_t l) {
    trim(&f);
    if (f.deg < 0) return 1;
    if (f.deg == 0) return 0;
    monic(&f, l);
    /* g = X^l mod f */
    poly g, base; g.deg = 0; g.c[0] = 1;
    base.deg = 1; base.c[0] = 0; base.c[1] = 1;
    pmod(&base, &f, l);
    for (uint64_t e = l; e; e >>= 1) {
        if (e & 1) pmulmod(&g, &g, &base, &f, l);
        pmulmod(&base, &base, &base, &f, l);
    }
    /* g - X */
    if (g.deg < 1) { for (int i = g.deg + 1; i <= 1; i++) g.c[i] = 0; g.deg = 1; }
    g.c[1] = (g.c[1] + l - 1) % l;
    trim(&g);
    /* gcd(f, g) */
    poly a = f, b = g;
    while (b.deg >= 0) {
        monic(&b, l);
        pmod(&a, &b, l);
        poly t = a; a = b; b = t;
    }
    return a.deg >= 1;
}

int main(void) {
    int n = 0;
    for (uint64_t c = (1ULL << 31) + 1; n < NP; c += 2) if (isprime(c)) P[n++] = c;
    int k, j, m;
    uint64_t x0, x1, M, a;
    while (scanf("%d %d %d %lu %lu %lu %lu", &k, &j, &m, &x0, &x1, &M, &a) == 7) {
        uint64_t d[KMAX], s[KMAX];
        for (int i = 0; i < k - 1; i++) if (scanf("%lu", &d[i]) != 1) return 1;
        int ix = k - 1 - j, h = 0;
        for (int i = 0; i < k; i++) s[i] = (i == ix) ? 0 : d[h++];
        uint64_t first = x0 + ((a % M) + M - x0 % M) % M, tested = 0;
        uint64_t count = first > x1 ? 0 : (x1 - first) / M + 1;
        #pragma omp parallel for schedule(dynamic, 4096) reduction(+:tested)
        for (uint64_t t = 0; t < count; t++) {
            uint64_t x = first + t * M;
            tested++;
            int i;
            for (i = 0; i < NP; i++) {
                uint64_t l = P[i], W = 0;
                for (int u = 0; u < k; u++)
                    if (u != ix) W = (W + (s[u] == 0 ? (uint64_t)m % l : powm(s[u], s[u], l))) % l;
                poly f; f.deg = k - 1;
                for (int u = 0; u < k; u++) f.c[k - 1 - u] = (u == ix ? x : s[u]) % l;
                uint64_t T = (W + powm(x % l, x, l)) % l;
                f.c[0] = (f.c[0] + l - T) % l;
                if (!hasroot(f, l)) break;
            }
            if (i == NP) {
                #pragma omp critical
                {
                    printf("survivor %d %d %d", k, j, m);
                    for (int u = 0; u < k - 1; u++) printf(" %lu", d[u]);
                    printf(" %lu\n", x);
                }
            }
        }
        printf("family %d %d %d", k, j, m);
        for (int u = 0; u < k - 1; u++) printf(" %lu", d[u]);
        printf(" x %lu..%lu mod %lu = %lu tested %lu\n", x0, x1, M, a % M, tested);
        fflush(stdout);
    }
    return 0;
}
