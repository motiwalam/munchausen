/* Round 6, k-length: sieve k-digit strings with k - 1 fixed small digits
   and one large digit x at a fixed position.

   Write the string most significant first; x multiplies b^j (j = 0 is
   the last position, j = k - 1 the leading one). With w(0) = m and
   w(d) = d^d, the string is a solution in base b exactly when

       Ps(b) + x b^j = W + x^x,

   where Ps is the polynomial of the small digits (x replaced by 0) and W
   the sum of their weights. For each prime l the program tabulates, for
   r = x mod l(l - 1), whether some b mod l satisfies this congruence
   (x^x mod l depends on x mod l and x mod l - 1). x survives when every
   one of the first NP primes allows it. The first six primes form a wheel
   of period 60060. Only x == a (mod M) in [x0, x1] are tested.

   input lines:  k j m x0 x1 M a d_1 ... d_(k-1)
                 (d_i the small digits, most significant first)
   output: "survivor k j m d_1 ... d_(k-1) x" for each survivor, then one
           line per family with the number of x tested.

   build: gcc -O3 -march=native -fopenmp -o r6k_sieve r6k_sieve.c
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define NP 120
#define NW 6
#define WHEEL 60060
#define KMAX 16
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
    for (uint32_t c = 2; n < NP; c++) {
        int pr = 1;
        for (uint32_t d = 2; d * d <= c; d++)
            if (c % d == 0) { pr = 0; break; }
        if (pr) P[n++] = c;
    }
    uint8_t *wheel = malloc(WHEEL);
    uint8_t *tab[NP];
    for (int i = 0; i < NP; i++) tab[i] = malloc((uint64_t)P[i] * (P[i] - 1) + 2);
    int k, j, m;
    uint64_t x0, x1, M, a;
    while (scanf("%d %d %d %lu %lu %lu %lu", &k, &j, &m, &x0, &x1, &M, &a) == 7) {
        uint64_t d[KMAX];
        for (int i = 0; i < k - 1; i++)
            if (scanf("%lu", &d[i]) != 1) return 1;
        /* full digit list, most significant first, slot ix holds x */
        int ix = k - 1 - j;
        uint64_t s[KMAX];
        int h = 0;
        for (int i = 0; i < k; i++) s[i] = (i == ix) ? 0 : d[h++];
        #pragma omp parallel for schedule(dynamic, 1)
        for (int i = 0; i < NP; i++) {
            uint64_t l = P[i], L = l * (l - 1);
            if (L == 0) L = 1;
            uint64_t W = 0;
            for (int t = 0; t < k; t++)
                if (t != ix) W = (W + wmod(s[t], m, l)) % l;
            uint64_t *ps = malloc(l * sizeof *ps), *bj = malloc(l * sizeof *bj);
            for (uint64_t b = 0; b < l; b++) {
                uint64_t v = 0;
                for (int t = 0; t < k; t++) v = (v * b + (t == ix ? 0 : s[t] % l)) % l;
                ps[b] = v;
                bj[b] = powmod(b, j, l);
            }
            /* img[xl * l + T] = 1 if Ps(b) + xl b^j == T for some b */
            uint8_t *img = calloc(l * l, 1);
            for (uint64_t b = 0; b < l; b++) {
                uint64_t v = ps[b];
                for (uint64_t xl = 0; xl < l; xl++) {
                    img[xl * l + v] = 1;
                    v += bj[b];
                    if (v >= l) v -= l;
                }
            }
            /* pw[u * (l - 1) + e] = u^e mod l */
            uint32_t *pw = malloc(l * (l - 1) * sizeof *pw + 4);
            for (uint64_t u = 0; u < l; u++) {
                uint64_t v = 1;
                for (uint64_t e = 0; e < l - 1; e++) {
                    pw[u * (l - 1) + e] = v;
                    v = v * u % l;
                }
            }
            uint64_t xl = 0, e = 0;
            for (uint64_t r = 0; r < L; r++) {
                uint64_t xx = xl == 0 ? 0 : pw[xl * (l - 1) + e];
                uint64_t T = W + xx;
                if (T >= l) T -= l;
                tab[i][r] = img[xl * l + T];
                if (++xl == l) xl = 0;
                if (++e == l - 1) e = 0;
            }
            free(ps); free(bj); free(img); free(pw);
        }
        for (uint64_t r = 0; r < WHEEL; r++) {
            uint8_t ok = 1;
            for (int i = 0; i < NW; i++) {
                uint64_t L = (uint64_t)P[i] * (P[i] - 1);
                ok &= tab[i][r % L];
            }
            wheel[r] = ok;
        }
        /* first x >= x0 with x == a mod M */
        uint64_t first = x0 + ((a % M) + M - x0 % M) % M;
        uint64_t count = first > x1 ? 0 : (x1 - first) / M + 1;
        uint64_t CH = 1 << 20;
        uint64_t nch = (count + CH - 1) / CH;
        uint64_t tested = 0;
        #pragma omp parallel for schedule(dynamic, 1) reduction(+:tested)
        for (uint64_t c = 0; c < nch; c++) {
            uint64_t i0 = c * CH, i1 = i0 + CH < count ? i0 + CH : count;
            uint64_t x = first + i0 * M;
            uint64_t r = x % WHEEL, step = M % WHEEL;
            for (uint64_t t = i0; t < i1; t++, x += M) {
                tested++;
                if (wheel[r]) {
                    int i;
                    for (i = NW; i < NP; i++) {
                        uint64_t L = (uint64_t)P[i] * (P[i] - 1);
                        if (!tab[i][x % L]) break;
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
                r += step;
                if (r >= WHEEL) r -= WHEEL;
            }
        }
        printf("family %d %d %d", k, j, m);
        for (int u = 0; u < k - 1; u++) printf(" %lu", d[u]);
        printf(" x %lu..%lu mod %lu = %lu tested %lu\n", x0, x1, M, a % M, tested);
        fflush(stdout);
    }
    return 0;
}
