/* Sieve for the Brocard-type cases of 3-digit factorions (round 6, question 97).

   Each input line "x c s ..." asks whether T = c * x! + s^2 is a perfect square.
   (The rest of the line is copied to the output.) For a prime l > x, x! is a
   unit mod l, and T must be a square mod l. The program takes the NP primes
   above the largest x, runs x! mod l for every x up to that maximum, and
   prints the candidates that are squares modulo all NP primes. A candidate
   that fails at one prime is not a square. Expected survivors of a random
   non-square: 2^-NP each.

   gcc -O2 -o r6f_brocard analysis/r6f_brocard.c
   ./r6f_brocard < analysis/data/r6f_brocard_cand.txt > analysis/data/r6f_brocard.txt
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define NP 40

typedef struct {
    uint64_t x, c, s;
    char rest[96];
} cand_t;

static int cmpc(const void *a, const void *b) {
    const cand_t *u = a, *v = b;
    return (u->x > v->x) - (u->x < v->x);
}

static int is_prime(uint64_t n) {
    if (n < 2) return 0;
    for (uint64_t d = 2; d * d <= n; d++)
        if (n % d == 0) return 0;
    return 1;
}

static uint64_t powmod(uint64_t a, uint64_t e, uint64_t m) {
    uint64_t r = 1;
    a %= m;
    while (e) {
        if (e & 1) r = r * a % m;
        a = a * a % m;
        e >>= 1;
    }
    return r;
}

int main(void) {
    size_t cap = 1 << 16, n = 0;
    cand_t *C = malloc(cap * sizeof(cand_t));
    char line[256];
    while (fgets(line, sizeof line, stdin)) {
        if (line[0] == '#') continue;
        if (n == cap) {
            cap *= 2;
            C = realloc(C, cap * sizeof(cand_t));
        }
        int off = 0;
        unsigned long long x, c, s;
        if (sscanf(line, "%llu %llu %llu %n", &x, &c, &s, &off) < 3) continue;
        C[n].x = x;
        C[n].c = c;
        C[n].s = s;
        strncpy(C[n].rest, line + off, sizeof C[n].rest - 1);
        C[n].rest[sizeof C[n].rest - 1] = 0;
        char *nl = strchr(C[n].rest, '\n');
        if (nl) *nl = 0;
        n++;
    }
    if (n == 0) {
        printf("# no candidates\n");
        return 0;
    }
    qsort(C, n, sizeof(cand_t), cmpc);
    uint64_t X = C[n - 1].x;
    uint64_t P[NP], f[NP];
    uint64_t p = X + 1;
    for (int i = 0; i < NP; i++) {
        while (!is_prime(p)) p++;
        P[i] = p++;
        f[i] = 1;
    }
    printf("# %zu candidates, largest x = %llu, primes %llu .. %llu\n", n,
           (unsigned long long)X, (unsigned long long)P[0], (unsigned long long)P[NP - 1]);
    size_t j = 0, survivors = 0;
    for (uint64_t x = 1; x <= X && j < n; x++) {
        for (int i = 0; i < NP; i++) f[i] = f[i] * (x % P[i]) % P[i];
        while (j < n && C[j].x == x) {
            int ok = 1;
            for (int i = 0; i < NP && ok; i++) {
                uint64_t l = P[i];
                uint64_t T = ((C[j].c % l) * f[i] % l + (C[j].s % l) * (C[j].s % l)) % l;
                if (T != 0 && powmod(T, (l - 1) / 2, l) != 1) ok = 0;
            }
            if (ok) {
                survivors++;
                printf("survivor x=%llu c=%llu s=%llu %s\n", (unsigned long long)C[j].x,
                       (unsigned long long)C[j].c, (unsigned long long)C[j].s, C[j].rest);
            }
            j++;
        }
    }
    printf("# survivors: %zu of %zu\n", survivors, n);
    return 0;
}
