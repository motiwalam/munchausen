/* Local sieve for b(b+x) = x^x + 1, the (1,x,1) equation of question 12.
 *
 * A solution needs f(x) = 4 x^x + x^2 + 4 to be a perfect square (f = (2b+x)^2).
 * For each x in [2, X], try the primes p < 65536 in order and stop at the first
 * p for which f(x) mod p is a nonzero quadratic nonresidue. Such an x is proven
 * to give no solution. x^x mod p only needs x mod p and x mod (p-1).
 * Prints every survivor (x that no prime excludes; these need an exact check)
 * and the number of x that survive the first k primes, for k = 1..40.
 *
 * Also prints the largest prime that was needed to exclude some x.
 * build: cc -O2 -o alg_sieve171 alg_sieve171.c
 * usage: alg_sieve171 X1 [X0]   (checks X0 <= x <= X1, default X0 = 2)
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#define PMAX 65536
static int primes[PMAX], np;
static unsigned char *qr[PMAX];

static uint32_t powmod(uint32_t a, uint32_t e, uint32_t p) {
    uint64_t r = 1, b = a % p;
    while (e) { if (e & 1) r = r * b % p; b = b * b % p; e >>= 1; }
    return (uint32_t)r;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: alg_sieve171 X1 [X0]\n"); return 1; }
    uint64_t X = strtoull(argv[1], 0, 10), X0 = argc > 2 ? strtoull(argv[2], 0, 10) : 2;
    int kmax = 0; uint64_t xkmax = 0;
    char *comp = calloc(PMAX, 1);
    for (int i = 2; i < PMAX; i++) {
        if (comp[i]) continue;
        primes[np++] = i;
        for (int j = 2 * i; j < PMAX; j += i) comp[j] = 1;
    }
    for (int i = 1; i < np; i++) {          /* odd primes; p = 2 never excludes */
        int p = primes[i];
        qr[i] = calloc(p, 1);
        for (uint64_t y = 0; y < (uint64_t)p; y++) qr[i][y * y % p] = 1;
    }
    uint64_t surv[41] = {0};
    for (uint64_t x = X0; x <= X; x++) {
        int k, dead = 0;
        for (k = 1; k < np; k++) {
            uint32_t p = primes[k];
            uint32_t a = x % p;
            uint32_t xx = a ? powmod(a, (uint32_t)(x % (p - 1)) + (p - 1), p) : 0;
            uint64_t f = (4ull * xx + (uint64_t)a * a + 4) % p;
            if (!qr[k][f]) { dead = 1; break; }
        }
        for (int j = 1; j <= 40 && j < k; j++) surv[j]++;
        if (dead && k > kmax) { kmax = k; xkmax = x; }
        if (!dead) printf("survivor %llu\n", (unsigned long long)x);
    }
    uint64_t cnt = X - X0 + 1;
    for (int j = 1; j <= 40; j++)
        printf("after %d odd primes: %llu of %llu survive (share %.3e)\n", j,
               (unsigned long long)surv[j], (unsigned long long)cnt, (double)surv[j] / cnt);
    printf("largest prime needed: %d (for x = %llu)\n", kmax < np ? primes[kmax] : -1, (unsigned long long)xkmax);
    return 0;
}
