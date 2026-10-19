// fixbase: for each base b in [b1, b2] list all n <= nmax such that 2^n is a palindrome in base b.
// usage: fixbase b1 b2 nmax alphafile
//   alphafile: lines "b hi lo" with floor(2^128 * log(2)/log(b)) split into two 64-bit halves
//   (computed with mpmath).
// Stage 1: the last j1 digits (b^j1 <= 2^16) reversed must equal the leading j1 digits;
//          leading digits are read off theta_n = frac(n log_b 2) held in 128-bit fixed point.
// Stage 2: same with j2 digits, b^j2 <= 1e17, via long double logarithms.
// Stage 3: exact verification (n <= NEXACT) or printed as CAND for external verification.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <string.h>
typedef unsigned __int128 u128;

static uint64_t dig[1 << 20];
static int exact_pal(long n, uint64_t b) {
    long K = 1; dig[0] = 1;
    int s = 1; while (s < 20 && ((u128)b << (s + 1)) < ((u128)1 << 63)) s++;
    long left = n;
    while (left > 0) {
        int t = left < s ? left : s; left -= t;
        u128 carry = 0;
        for (long i = 0; i < K; i++) {
            u128 v = ((u128)dig[i] << t) + carry;
            dig[i] = (uint64_t)(v % b); carry = v / b;
        }
        while (carry) { dig[K++] = (uint64_t)(carry % b); carry /= b; }
    }
    for (long i = 0, j = K - 1; i < j; i++, j--) if (dig[i] != dig[j]) return 0;
    return 1;
}

int main(int argc, char **argv) {
    uint64_t b1 = strtoull(argv[1], 0, 10), b2 = strtoull(argv[2], 0, 10);
    long nmax = atol(argv[3]);
    FILE *af = fopen(argv[4], "r");
    static uint64_t AH[1 << 20], AL[1 << 20];
    uint64_t bb, h, l;
    while (fscanf(af, "%llu %llu %llu", (unsigned long long *)&bb, (unsigned long long *)&h, (unsigned long long *)&l) == 3)
        if (bb < (1 << 20)) { AH[bb] = h; AL[bb] = l; }
    fclose(af);
    for (uint64_t b = b1; b <= b2; b++) {
        if ((b & (b - 1)) == 0) continue;  // powers of 2: 2^n = (2^r,0,...,0), never a palindrome with >1 digit
        u128 alpha = ((u128)AH[b] << 64) | AL[b];
        // stage-1 parameters
        int j1 = 1; uint64_t P1 = b; while (P1 * b <= 65536) { P1 *= b; j1++; }
        uint64_t P1lo = P1 / b;   // b^(j1-1)
        // reverse table and thresholds: for v in [P1lo, P1], LT[v] = 2^64 (log_b v - (j1-1))
        static uint32_t REV[65536 + 1]; static uint64_t LT[65536 + 2];
        for (uint64_t w = 0; w < P1; w++) { uint64_t x = w, v = 0; for (int i = 0; i < j1; i++) { v = v * b + x % b; x /= b; } REV[w] = (uint32_t)v; }
        long double lb = logl((long double)b);
        for (uint64_t v = P1lo; v <= P1; v++) {
            long double fr = logl((long double)v) / lb - (long double)(j1 - 1);
            if (fr < 0) fr = 0;
            LT[v] = (fr >= 1.0L) ? UINT64_MAX : (uint64_t)(fr * 18446744073709551616.0L);
        }
        // stage-2 parameters
        int j2 = 1; uint64_t P2 = b; while ((long double)P2 * b <= 1e17L) { P2 *= b; j2++; }
        long nexact = (long)((2 * j2 + 2) * log2((double)b)) + 2; if (nexact < 64) nexact = 64;
        const uint64_t EPS = (uint64_t)1 << 22;  // ~2^-42 margin on theta (64-bit view)
        uint64_t w1 = 1 % P1, w2 = 1 % P2; u128 theta = 0;
        long found = 0, cands = 0;
        for (long n = 0; n <= nmax; n++) {
            if (n <= nexact) {
                if (n >= 1 && exact_pal(n, b)) { printf("PAL b=%llu n=%ld\n", (unsigned long long)b, n); found++; }
            } else {
                uint64_t v = REV[w1];
                if (v >= P1lo) {
                    uint64_t th = (uint64_t)(theta >> 64);
                    uint64_t lo = LT[v], hi = (v + 1 <= P1) ? LT[v + 1] : UINT64_MAX;
                    int ok = ((u128)th + EPS >= (u128)lo) && ((u128)th < (u128)hi + EPS);
                    if (ok) {
                        // stage 2
                        uint64_t x = w2, rv = 0; for (int i = 0; i < j2; i++) { rv = rv * b + x % b; x /= b; }
                        if (rv >= P2 / b) {
                            long double t2 = (long double)th / 18446744073709551616.0L;
                            long double L = logl((long double)rv) / lb - (j2 - 1), H = logl((long double)rv + 1) / lb - (j2 - 1);
                            if (t2 >= L - 1e-15L && t2 < H + 1e-15L) {
                                cands++;
                                if (n <= 200000) { if (exact_pal(n, b)) { printf("PAL b=%llu n=%ld\n", (unsigned long long)b, n); found++; } }
                                else printf("CAND b=%llu n=%ld\n", (unsigned long long)b, n);
                            }
                        }
                    }
                }
            }
            w1 <<= 1; if (w1 >= P1) w1 -= P1;
            w2 <<= 1; if (w2 >= P2) w2 -= P2;
            theta += alpha;
        }
        printf("BASE b=%llu nmax=%ld found=%ld stage2cands=%ld j1=%d j2=%d\n", (unsigned long long)b, nmax, found, cands, j1, j2);
        fflush(stdout);
    }
    return 0;
}
