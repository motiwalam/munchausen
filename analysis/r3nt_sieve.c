/* Local sieve for f(x) = A x^e + B x^2 + C x + D = square, questions 51 and 52.
 *
 * The exponent e is x itself (families (1,x,r) and (1,2,x)) or a fixed n.
 * For each x in [X0, X1] the program tries the modulus 64 and then the odd
 * primes p < 65536 in order, and stops at the first one for which f(x) is not
 * a square mod p (or mod 64). Such an x gives no solution. x^e mod p only
 * needs x mod p and e mod (p - 1). Every survivor is printed; it needs an
 * exact check.
 *
 * families:
 *   (1,x,2): 4 x^x + x^2 + 12 = (2b + x)^2      A=4 B=1 C=0 D=12
 *   (1,x,3): 4 x^x + x^2 + 100 = (2b + x)^2     A=4 B=1 C=0 D=100
 *   (1,2,x): x^x - x + 6 = (b + 1)^2            A=1 B=0 C=-1 D=6
 *   n fixed: 4 x^n + x^2 + 4 = (2b + x)^2       A=4 B=1 C=0 D=4, e = n
 * build: cc -O2 -o fast/target/r3nt_sieve analysis/r3nt_sieve.c
 * usage: r3nt_sieve A B C D e X1 [X0] [step] [offset]
 *   e = 0 means e = x; only x == offset (mod step) are tested (default 1, 0)
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#define PMAX 65536
static int primes[PMAX], np;
static unsigned char *qr[PMAX];
static unsigned char qr64[64];

static uint64_t powmod(uint64_t a, uint64_t e, uint64_t m) {
    uint64_t r = 1 % m, b = a % m;
    while (e) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; }
    return r;
}

static int64_t mod(int64_t a, int64_t m) { a %= m; return a < 0 ? a + m : a; }

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: r3nt_sieve A B C D e X1 [X0] [step] [offset]\n"); return 1; }
    int64_t A = atoll(argv[1]), B = atoll(argv[2]), C = atoll(argv[3]), D = atoll(argv[4]);
    uint64_t e = strtoull(argv[5], 0, 10);
    uint64_t X1 = strtoull(argv[6], 0, 10);
    uint64_t X0 = argc > 7 ? strtoull(argv[7], 0, 10) : 2;
    uint64_t step = argc > 8 ? strtoull(argv[8], 0, 10) : 1;
    uint64_t off = argc > 9 ? strtoull(argv[9], 0, 10) : 0;
    char *comp = calloc(PMAX, 1);
    for (int i = 2; i < PMAX; i++) {
        if (comp[i]) continue;
        primes[np++] = i;
        for (int j = 2 * i; j < PMAX; j += i) comp[j] = 1;
    }
    for (int i = 1; i < np; i++) {
        int p = primes[i];
        qr[i] = calloc(p, 1);
        for (uint64_t y = 0; y < (uint64_t)p; y++) qr[i][y * y % p] = 1;
    }
    for (int y = 0; y < 64; y++) qr64[y * y % 64] = 1;
    uint64_t tested = 0, nsurv = 0, by64 = 0;
    int kmax = 0; uint64_t xkmax = 0;
    uint64_t x = X0 + mod((int64_t)off - (int64_t)(X0 % step), step);
    for (; x <= X1; x += step) {
        tested++;
        uint64_t ex = e ? e : x;
        /* modulus 64: x^ex mod 64; for even x and ex >= 6 it is 0 */
        uint64_t a64 = x % 64, xx64;
        if (x % 2 == 0) xx64 = ex >= 6 ? 0 : powmod(a64, ex, 64);
        else xx64 = powmod(a64, ex % 16 + 16, 64);
        int64_t f64 = mod(A * (int64_t)xx64 + B * (int64_t)(a64 * a64 % 64) + C * (int64_t)a64 + D, 64);
        if (!qr64[f64]) { by64++; continue; }
        int k, dead = 0;
        for (k = 1; k < np; k++) {
            uint64_t p = primes[k];
            uint64_t a = x % p;
            uint64_t xx = a ? powmod(a, ex % (p - 1) + (p - 1), p) : (ex ? 0 : 1);
            int64_t f = mod(A * (int64_t)xx + B * (int64_t)(a * a % p) + C * (int64_t)a + D, p);
            if (!qr[k][f]) { dead = 1; break; }
        }
        if (dead && k > kmax) { kmax = k; xkmax = x; }
        if (!dead) { nsurv++; printf("survivor %llu\n", (unsigned long long)x); }
    }
    printf("tested %llu values of x in [%llu, %llu] (step %llu, offset %llu): %llu excluded mod 64, "
           "%llu survivors; largest prime needed %d (x = %llu)\n",
           (unsigned long long)tested, (unsigned long long)X0, (unsigned long long)X1,
           (unsigned long long)step, (unsigned long long)off, (unsigned long long)by64,
           (unsigned long long)nsurv, kmax ? primes[kmax] : 0, (unsigned long long)xkmax);
    return 0;
}
