/* Sieve for b (b + x) = x^n + 1 with a fixed exponent n (question 32).
 * A solution needs f(x) = 4 x^n + x^2 + 4 to be a perfect square.
 * For every x in [2, X] the program looks for a modulus m (64 or an odd
 * prime below 2000) with f(x) a non-square mod m. Survivors are checked
 * exactly with GMP and printed.
 * build: gcc -O2 -o fast/target/r2nt_sieve_n analysis/r2nt_sieve_n.c -lgmp
 * usage: r2nt_sieve_n n X
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <gmp.h>

#define NP 300
static int primes[NP];
static unsigned char *ok[NP];
static unsigned char ok64[64];

static uint64_t powmod(uint64_t a, uint64_t e, uint64_t m) {
    uint64_t r = 1 % m; a %= m;
    while (e) { if (e & 1) r = r * a % m; a = a * a % m; e >>= 1; }
    return r;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s n X\n", argv[0]); return 1; }
    long n = atol(argv[1]);
    uint64_t X = strtoull(argv[2], 0, 10);
    int np = 0;
    for (int p = 3; np < NP; p += 2) {
        int isp = 1;
        for (int q = 3; q * q <= p; q += 2) if (p % q == 0) { isp = 0; break; }
        if (!isp) continue;
        primes[np] = p;
        unsigned char *sq = calloc(p, 1);
        for (int t = 0; t < p; t++) sq[(uint64_t)t * t % p] = 1;
        ok[np] = malloc(p);
        for (int r = 0; r < p; r++) {
            uint64_t f = (4 * powmod(r, n, p) + (uint64_t)r * r + 4) % p;
            ok[np][r] = sq[f];
        }
        free(sq);
        np++;
    }
    {
        unsigned char sq[64] = {0};
        for (int t = 0; t < 64; t++) sq[t * t % 64] = 1;
        for (int r = 0; r < 64; r++) {
            uint64_t f = (4 * powmod(r, n, 64) + (uint64_t)r * r + 4) % 64;
            ok64[r] = sq[f];
        }
    }
    uint64_t survivors = 0, hits = 0;
    int maxused = 0;
    mpz_t f, t;
    mpz_init(f); mpz_init(t);
    for (uint64_t x = 2; x <= X; x++) {
        if (!ok64[x & 63]) continue;
        int i;
        for (i = 0; i < np; i++) {
            if (!ok[i][x % primes[i]]) break;
        }
        if (i < np) { if (i > maxused) maxused = i; continue; }
        survivors++;
        mpz_set_ui(f, x);
        mpz_pow_ui(f, f, n);
        mpz_mul_ui(f, f, 4);
        mpz_set_ui(t, x); mpz_mul_ui(t, t, x); mpz_add_ui(t, t, 4);
        mpz_add(f, f, t);
        if (mpz_perfect_square_p(f)) { hits++; printf("solution n=%ld x=%llu\n", n, (unsigned long long)x); }
        else printf("survivor (not a square) n=%ld x=%llu\n", n, (unsigned long long)x);
    }
    printf("n=%ld X=%llu survivors=%llu solutions=%llu largest prime used=%d\n", n,
           (unsigned long long)X, (unsigned long long)survivors, (unsigned long long)hits,
           primes[maxused]);
    return 0;
}
