// Question 80: rho(b) = max over L in [Lmin, b] and h mod m outside H_0 of
// |psi_L(h)|, psi_L(h) = (1/L) sum_{x<L} e(h g(x) / m), m = b - 1,
// g(x) = x^x - x for x >= 1, g(0) = 0. H_0 = {0, m/2} for even m, {0} for odd m.
// Also reports the Poisson rate min over the same set of 1 - Re psi_L(h).
// Lmin = ceil(b/2) (the digit ranges of Theorem 3.3 in round5-model.md).
//
// build: gcc -O2 -fopenmp -o r5m_rho r5m_rho.c -lm
// usage: r5m_rho BMIN BMAX > out
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

static long powmod(long a, long e, long m) {
    long r = 1 % m;
    a %= m;
    while (e) {
        if (e & 1) r = r * a % m;
        a = a * a % m;
        e >>= 1;
    }
    return r;
}

int main(int argc, char **argv) {
    int bmin = atoi(argv[1]), bmax = atoi(argv[2]);
    int nb = bmax - bmin + 1;
    double *rho = malloc(sizeof(double) * nb), *cp = malloc(sizeof(double) * nb);
    int *argL = malloc(sizeof(int) * nb), *argh = malloc(sizeof(int) * nb);
#pragma omp parallel for schedule(dynamic, 1)
    for (int b = bmax; b >= bmin; b--) {
        long m = b - 1;
        double *co = malloc(sizeof(double) * m), *si = malloc(sizeof(double) * m);
        double *zr = calloc(m, sizeof(double)), *zi = calloc(m, sizeof(double));
        for (long k = 0; k < m; k++) {
            co[k] = cos(2 * M_PI * k / m);
            si[k] = sin(2 * M_PI * k / m);
        }
        int lmin = (b + 1) / 2;
        double best = 0, bestc = 2;
        int bl = 0, bh = 0;
        for (int L = 1; L <= b; L++) {
            long x = L - 1;
            long g = x == 0 ? 0 : ((powmod(x, x, m) - x) % m + m) % m;
            long idx = 0;
            for (long h = 0; h < m; h++) {
                zr[h] += co[idx];
                zi[h] += si[idx];
                idx += g;
                if (idx >= m) idx -= m;
            }
            if (L >= lmin) {
                for (long h = 1; h < m; h++) {
                    if (m % 2 == 0 && 2 * h == m) continue;
                    double a = sqrt(zr[h] * zr[h] + zi[h] * zi[h]) / L;
                    double c = 1 - zr[h] / L;
                    if (a > best) { best = a; bl = L; bh = (int)h; }
                    if (c < bestc) bestc = c;
                }
            }
        }
        rho[b - bmin] = best;
        cp[b - bmin] = bestc;
        argL[b - bmin] = bl;
        argh[b - bmin] = bh;
        free(co); free(si); free(zr); free(zi);
    }
    printf("# b rho=max|psi_L(h)| L h  min(1-Re psi_L(h))   L in [ceil(b/2), b], h not in H_0, m = b-1\n");
    for (int b = bmin; b <= bmax; b++)
        printf("%d %.6f %d %d %.6f\n", b, rho[b - bmin], argL[b - bmin], argh[b - bmin], cp[b - bmin]);
    return 0;
}
