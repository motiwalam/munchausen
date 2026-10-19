/* Round 4, blocks: the defect spectrum of short strings, base by base.

   For each base b in [bmin, bmax], enumerate every string t of L digits
   (leading digit >= 1, digits up to X_b) and compute

       V = b^m P_t(b) - F(t),

   where F counts the weights of the L digits of t only (0^0 = mode). With
   m = 0 this is n - F(n) for the L-digit numbers; with m >= 1 it is the
   remainder of t as a block at shift m. X_b is the largest digit x < b with
   x^x <= b^(L+m) + W, so every string with |V| <= W is seen.

   For the strings with |V| <= W = floor(wfrac * b^(L+m-1)) it records:
     - N_0, the count with V = 0, and the strings themselves;
     - a histogram of V for |V| <= H;
     - for E <= |V| <= W (E = b), the total count and the count with
       V == 0 mod q for each modulus q of a list, and mod 2(b-1).
   The analysis (r4b_spectrum.py) turns these into the expected N_0.

   usage: r4b_spectrum L m mode bmin bmax [wfrac] [H]
   Output: one line per base, "B b X W E nstr N0 tot cls2b1 ncls2b1 q:count ...",
   a line "C b M:count:offsets ..." for classes mod multiples M of 2(b-1),
   then "S b digits" for each string with V = 0 and "H b v:count ..." for the
   histogram. Build: gcc -O2 -fopenmp -o r4b_spectrum r4b_spectrum.c
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

typedef long long ll;
typedef __int128 i128;

#define MAXL 12
#define MAXQ 16
#define MAXH 2000

static int L, m, mode;
static double wfrac = 0.05;
static int H = 300;

struct ctx {
    int b, X;
    ll W, E;
    ll c[MAXL][128];         /* c[i][x] = x b^(m+i) - w(x), position m+i */
    ll lo[MAXL + 1], hi[MAXL + 1]; /* bounds on the sum of positions 0..i-1 */
    int nq;
    ll q[MAXQ];
    ll cnt[MAXQ];
    ll tot, cls, n0, nstr;
    ll M2;                   /* 2(b-1) */
    int nc;
    ll cm[MAXQ];             /* class moduli, multiples of 2(b-1) */
    ll ccnt[MAXQ];
    ll hist[2 * MAXH + 1];
    int digits[MAXL];
    char *sols;
    size_t solen, solcap;
};

static ll ipow(ll a, int e) { ll r = 1; while (e--) r *= a; return r; }

static void record(struct ctx *C, ll V) {
    if (V >= -H && V <= H) C->hist[V + H]++;
    if (V == 0) {
        C->n0++;
        char buf[256];
        int p = snprintf(buf, sizeof buf, "S %d", C->b);
        for (int i = L - 1; i >= 0; i--) p += snprintf(buf + p, sizeof buf - p, "%s%d", i == L - 1 ? " " : ",", C->digits[i]);
        p += snprintf(buf + p, sizeof buf - p, "\n");
        if (C->solen + p + 1 > C->solcap) {
            C->solcap = 2 * (C->solen + p + 1);
            C->sols = realloc(C->sols, C->solcap);
        }
        memcpy(C->sols + C->solen, buf, p + 1);
        C->solen += p;
        return;
    }
    ll a = V < 0 ? -V : V;
    if (a < C->E) return;
    C->tot++;
    if (V % C->M2 == 0) {
        C->cls++;
        for (int j = 0; j < C->nc; j++)
            if (V % C->cm[j] == 0) C->ccnt[j]++;
    }
    for (int j = 0; j < C->nq; j++)
        if (V % C->q[j] == 0) C->cnt[j]++;
}

/* fill digit i (from the top, index L-1) down to 0 */
static void rec(struct ctx *C, int i, ll partial) {
    if (i < 0) {
        C->nstr++;
        if (partial >= -C->W && partial <= C->W) record(C, partial);
        return;
    }
    int x0 = (i == L - 1) ? 1 : 0;
    for (int x = x0; x <= C->X; x++) {
        ll v = partial + C->c[i][x];
        /* the lower positions add between lo[i] and hi[i] */
        if (v + C->lo[i] > C->W || v + C->hi[i] < -C->W) continue;
        C->digits[i] = x;
        rec(C, i - 1, v);
    }
}

static ll gcd(ll a, ll b) { while (b) { ll t = a % b; a = b; b = t; } return a; }
static ll lcm(ll a, ll b) { return a / gcd(a, b) * b; }

static void add_q(struct ctx *C, ll q) {
    for (int j = 0; j < C->nq; j++) if (C->q[j] == q) return;
    C->q[C->nq++] = q;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: r4b_spectrum L m mode bmin bmax [wfrac] [H]\n");
        return 1;
    }
    L = atoi(argv[1]); m = atoi(argv[2]); mode = atoi(argv[3]);
    int bmin = atoi(argv[4]), bmax = atoi(argv[5]);
    if (argc > 6) wfrac = atof(argv[6]);
    if (argc > 7) H = atoi(argv[7]);
    int k = L + m;
    int nb = bmax - bmin + 1;
    struct ctx *all = calloc(nb, sizeof(struct ctx));
    printf("# r4b_spectrum L=%d m=%d mode=%d bases %d-%d wfrac=%g H=%d\n", L, m, mode, bmin, bmax, wfrac, H);
    printf("# B b X W E strings N0 tot cls_2(b-1) nclass_2(b-1) q:count ...  (counts over E <= |V| <= W)\n");
    fflush(stdout);
#pragma omp parallel for schedule(dynamic, 1)
    for (int bi = 0; bi < nb; bi++) {
        struct ctx *C = &all[bi];
        int b = bmin + bi;
        C->b = b;
        double bk = pow((double)b, k);
        C->W = (ll)floor(wfrac * pow((double)b, k - 1));
        if (C->W < 1) C->W = 1;
        C->E = b;
        int X = 0;
        for (int x = 1; x < b && x < 128; x++)
            if (x * log((double)x) <= log(bk + C->W) + 1e-12) X = x;
        C->X = X;
        for (int i = 0; i < L; i++) {
            ll bp = ipow(b, m + i);
            for (int x = 0; x <= X; x++) {
                ll wx = x == 0 ? mode : ipow(x, x);
                C->c[i][x] = (ll)x * bp - wx;
            }
        }
        C->lo[0] = C->hi[0] = 0;
        for (int i = 0; i < L; i++) {
            ll mn = C->c[i][0], mx = C->c[i][0];
            for (int x = 1; x <= X; x++) {
                if (C->c[i][x] < mn) mn = C->c[i][x];
                if (C->c[i][x] > mx) mx = C->c[i][x];
            }
            C->lo[i + 1] = C->lo[i] + mn;
            C->hi[i + 1] = C->hi[i] + mx;
        }
        C->M2 = 2 * (ll)(b - 1);
        /* moduli: 16, 27, 25, 49, raised to the full power in b(b-1), and the
           prime powers of b(b-1) for primes >= 11 */
        ll bb = (ll)b * (b - 1);
        ll base_q[4] = {16, 27, 25, 49};
        ll ps[4] = {2, 3, 5, 7};
        for (int j = 0; j < 4; j++) {
            ll q = base_q[j], t = bb, pp = 1;
            while (t % ps[j] == 0) { t /= ps[j]; pp *= ps[j]; }
            add_q(C, q > pp ? q : pp);
        }
        ll t = bb;
        for (ll p = 2; p <= t; p++) {
            if (t % p) continue;
            ll pp = 1;
            while (t % p == 0) { t /= p; pp *= p; }
            if (p >= 11) add_q(C, pp);
        }
        /* class moduli: 2(b-1) times 4, 8, 9, 72, 1800, b, 16*27*25*49 */
        ll extra[7] = {4, 8, 9, 72, 1800, b, 16LL * 27 * 25 * 49};
        C->nc = 7;
        for (int j = 0; j < 7; j++) C->cm[j] = lcm(C->M2, extra[j]);
        rec(C, L - 1, 0);
    }
    for (int bi = 0; bi < nb; bi++) {
        struct ctx *C = &all[bi];
        ll ncls = 2 * ((C->W / C->M2) - ((C->E - 1) / C->M2));
        printf("B %d %d %lld %lld %lld %lld %lld %lld %lld", C->b, C->X, C->W, C->E, C->nstr, C->n0, C->tot, C->cls, ncls);
        for (int j = 0; j < C->nq; j++) printf(" %lld:%lld", C->q[j], C->cnt[j]);
        printf("\nC %d", C->b);
        for (int j = 0; j < C->nc; j++) {
            ll M = C->cm[j];
            ll nc = 2 * ((C->W / M) - ((C->E - 1) / M));
            printf(" %lld:%lld:%lld", M, C->ccnt[j], nc);
        }
        printf("\n");
        if (C->solen) fputs(C->sols, stdout);
        printf("H %d", C->b);
        for (int v = -H; v <= H; v++)
            if (C->hist[v + H]) printf(" %d:%lld", v, C->hist[v + H]);
        printf("\n");
    }
    return 0;
}
