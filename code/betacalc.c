// compute beta(n) for 1 <= n <= NMAX using log-binomials; print near-ties for exact recheck
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
int main(int argc, char **argv) {
    long NMAX = atol(argv[1]);
    long KM = NMAX + 2;
    long double *lc = malloc(sizeof(long double) * (KM + 1));   // log2 C(k, floor(k/2))
    for (long k = 0; k <= KM; k++) lc[k] = (lgammal(k + 1.0L) - lgammal(k / 2 + 1.0L) - lgammal(k - k / 2 + 1.0L)) / logl(2.0L);
    FILE *ties = fopen("beta_ties.txt", "w");
    for (long n = 1; n <= NMAX; n++) {
        long x;
        long xs = (long)floorl(sqrtl((long double)n) - (1.0L + 0.5L * log2l(2.0L * n + 2)) / 2) - 1;
        if (xs < 2) xs = 2;
        for (x = xs;; x++) {
            long k = n / x, r = n % x;
            long double lhs = r + lc[k], rhs = x + log1pl(-ldexpl(1.0L, -(int)x)) / logl(2.0L);
            long double d = rhs - lhs;
            if (fabsl(d) < 1e-9L) fprintf(ties, "%ld %ld\n", n, x);
            if (d > 0) break;
        }
        printf("%ld %ld\n", n, x);
    }
    fclose(ties);
    return 0;
}
