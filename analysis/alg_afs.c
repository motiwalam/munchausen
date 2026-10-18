/* Munchausen numbers in the rational base p/q of Akiyama, Frougny and
 * Sakarovitch (question 11).
 *
 * Every N >= 1 has a unique expansion N = sum_i (a_i / q) (p/q)^i with digits
 * a_i in [0, p-1], produced by q N_i = p N_{i+1} + a_i, N_0 = N. N is a
 * Munchausen number when N = sum_i w(a_i), w(a) = a^a and w(0) = m (0^0 = m).
 * F(N) <= L(N) (p-1)^(p-1) with L(N) the length, so N is bounded; the bound is
 * found by doubling. Prints every solution with N >= 2 for p <= PMAX.
 * build: cc -O2 -o alg_afs alg_afs.c    usage: alg_afs PMAX
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>

static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

int main(int argc, char **argv) {
    int PMAX = argc > 1 ? atoi(argv[1]) : 8;
    for (int p = 2; p <= PMAX; p++)
        for (int q = 1; q < p; q++) {
            if (gcd(p, q) != 1) continue;
            uint64_t w[2][16];
            for (int m = 0; m < 2; m++) {
                w[m][0] = m;
                for (int a = 1; a < p; a++) { uint64_t v = 1; for (int i = 0; i < a; i++) v *= a; w[m][a] = v; }
            }
            /* length of the expansion of N is at most log(N)/log(p/q) + 2 */
            double lr = log((double)p / q);
            uint64_t top = w[1][p - 1] > 1 ? w[1][p - 1] : 1, Nmax = 16;
            while ((double)Nmax < (log((double)Nmax) / lr + 3) * (double)top) Nmax *= 2;
            for (int m = 0; m < 2; m++)
                for (uint64_t N = 2; N <= Nmax; N++) {
                    uint64_t n = N, F = 0;
                    int digs[256], L = 0;
                    while (n) {
                        uint64_t t = (uint64_t)q * n;
                        int a = (int)(t % p);
                        n = (t - a) / p;
                        digs[L++] = a;
                        F += w[m][a];
                        if (F > N) break;
                    }
                    if (n == 0 && F == N) {
                        printf("p/q=%d/%d 0^0=%d N=%llu digits(most significant first)=", p, q, m, (unsigned long long)N);
                        for (int i = L - 1; i >= 0; i--) printf("%d%s", digs[i], i ? "," : "\n");
                    }
                }
            fprintf(stderr, "done p/q=%d/%d up to N=%llu\n", p, q, (unsigned long long)Nmax);
        }
    return 0;
}
