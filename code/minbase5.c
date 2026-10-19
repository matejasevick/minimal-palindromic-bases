// minbase5: exhaustive search for palindromic representations of 2^n in small bases.
//
// Mode "range":  minbase5 range N1 part nparts [plus1]
//    For every n <= N1 and every base 3 <= b < U(n) = 2^beta(n) - 1 test whether 2^n is a
//    palindrome in base b ("plus1": also include b = U(n), as a built-in positive control).
// Mode "single": minbase5 single n Bmax part nparts
//    Test every base 3 <= b < Bmax for the single exponent n.
//
// Method.  Bases are processed in blocks of BLK consecutive integers.  For base b the state
// (c, y) = (2^t mod b, 2^t / b^K) with 1 <= y < b (K = number of digits - 1) is initialised
// by a vectorised modular exponentiation and an interpolated leading part, and advanced by
// doubling (or by cheap jumps of up to 30 doublings).  2^t can be a palindrome in base b only
// if its last digit c equals its leading digit floor(y); this is tested with a safety margin
// that dominates all floating-point error, and every candidate is verified exactly.
// Bases not of the form 2^x - 1 are only tested when 2^t has an odd number of digits
// (Kreher-Stinson Lemma 2.2 / Cor. 2.3: an even-length palindrome is divisible by b + 1).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <string.h>

typedef unsigned __int128 u128;
#define BLK 512
#define GAP 2
#define NMAX 4096

static int beta[NMAX];
static uint64_t U[NMAX];

static uint64_t modpow2_slow(uint64_t e, uint64_t m) {
    uint64_t r = 1 % m, a = 2 % m;
    while (e) { if (e & 1) r = (u128)r * a % m; a = (u128)a * a % m; e >>= 1; }
    return r;
}
static uint64_t dig[16384];
// exact test: is 2^n a palindrome in base b ?
static int exact_pal(int n, uint64_t b) {
    int K = 1; dig[0] = 1;
    int s = 1; while (s < 20 && ((u128)b << (s + 1)) < ((u128)1 << 63)) s++;
    int left = n;
    while (left > 0) {
        int t = left < s ? left : s; left -= t;
        u128 carry = 0;
        for (int i = 0; i < K; i++) {
            u128 v = ((u128)dig[i] << t) + carry;
            dig[i] = (uint64_t)(v % b); carry = v / b;
        }
        while (carry) { dig[K++] = (uint64_t)(carry % b); carry /= b; }
    }
    for (int i = 0, j = K - 1; i < j; i++, j--) if (dig[i] != dig[j]) return 0;
    return 1;
}

static int64_t C[BLK], Bv[BLK];
static double Y[BLK], IB[BLK];
static long long ncand = 0, npal = 0, ninit = 0, njump = 0;
static long double steps = 0;

static void init_state(uint64_t B0, int cnt, int s) {
    for (int i = 0; i < cnt; i++) { int64_t b = (int64_t)(B0 + i); Bv[i] = b; IB[i] = 1.0 / (double)b; }
    ninit += cnt;
    if (B0 < 4096) {
        long double l2 = logl(2.0L);
        for (int i = 0; i < cnt; i++) {
            uint64_t b = B0 + i;
            long double lb = logl((long double)b);
            long double fr = (long double)s * l2 / lb; fr -= floorl(fr);
            double y = (double)expl(fr * lb);
            if (y >= (double)b) y /= (double)b;
            if (y < 1.0) y = 1.0;
            Y[i] = y; C[i] = (int64_t)modpow2_slow(s, b);
        }
        return;
    }
    long double L0 = (long double)s * logl(2.0L), lB0 = logl((long double)B0);
    long double K0 = floorl(L0 / lB0);
    long double y0l = expl(L0 - K0 * lB0);
    if (y0l >= (long double)B0) { y0l /= (long double)B0; K0 += 1; }
    if (y0l < 1.0L) { y0l *= (long double)B0; K0 -= 1; }
    double y0 = (double)y0l, K = (double)K0, iB0 = 1.0 / (double)B0;
    if (B0 < (1ULL << 24)) {
        for (int i = 0; i < cnt; i++) {
            double t = K * log1p((double)i * iB0);
            double y = y0 * exp(-t);
            while (y < 1.0) y *= (double)Bv[i];
            Y[i] = y;
        }
    } else {
        for (int i = 0; i < cnt; i++) {   // y0 * (B0/b)^K via series; u <= 2^-15
            double u = (double)i * iB0;
            double lg = u * (1.0 - u * (0.5 - u * (1.0 / 3 - u * 0.25)));
            double t = K * lg;
            double ex = 1.0 - t * (1.0 - t * (0.5 - t * (1.0 / 6 - t * (1.0 / 24 - t * (1.0 / 120 - t / 720)))));
            double y = y0 * ex;
            if (y < 1.0) y *= (double)Bv[i];
            Y[i] = y;
        }
    }
    int top = 31 - __builtin_clz((unsigned)s);
    for (int i = 0; i < cnt; i++) C[i] = 1;
    for (int bit = top; bit >= 0; bit--) {
        for (int i = 0; i < cnt; i++) {          // C <- C^2 mod b  (fp-assisted, exact)
            int64_t a = C[i], b = Bv[i];
            int64_t q = (int64_t)((double)a * (double)a * IB[i]);
            int64_t r = (int64_t)((uint64_t)a * (uint64_t)a - (uint64_t)q * (uint64_t)b);
            r += (r < 0) ? b : 0; r += (r < 0) ? b : 0;
            r -= (r >= b) ? b : 0; r -= (r >= b) ? b : 0;
            C[i] = r;
        }
        if ((s >> bit) & 1)
            for (int i = 0; i < cnt; i++) { int64_t c = C[i] << 1; C[i] = c >= Bv[i] ? c - Bv[i] : c; }
    }
}

static void advance(uint64_t B0, int cnt, int g) {
    njump++;
    if (B0 < 4096) {
        for (; g > 0; g--) for (int i = 0; i < cnt; i++) {
            int64_t c2 = C[i] << 1, b = Bv[i]; C[i] = c2 >= b ? c2 - b : c2;
            double y2 = Y[i] * 2.0; Y[i] = y2 >= (double)b ? y2 * IB[i] : y2;
        }
        return;
    }
    while (g > 0) {
        int h = g < 30 ? g : 30; g -= h;
        int64_t p = (int64_t)1 << h; double pd = (double)p;
        for (int i = 0; i < cnt; i++) {
            int64_t a = C[i], b = Bv[i]; double bd = (double)b;
            int64_t q = (int64_t)((double)a * pd * IB[i]);
            int64_t r = (int64_t)((uint64_t)a * (uint64_t)p - (uint64_t)q * (uint64_t)b);
            r += (r < 0) ? b : 0; r += (r < 0) ? b : 0;
            r -= (r >= b) ? b : 0; r -= (r >= b) ? b : 0;
            C[i] = r;
            double y = Y[i] * pd;
            y = y >= bd ? y * IB[i] : y;
            y = y >= bd ? y * IB[i] : y;
            y = y >= bd ? y * IB[i] : y;
            Y[i] = y;
        }
    }
}

// flag of lane i for the current state
static inline int lane_flag(int i) {
    double y = Y[i]; int64_t c = C[i], b = Bv[i]; double cd = (double)c, bd = (double)b;
    double tol = y * 3e-13 + 1e-9;
    if (c != 0 && y >= cd - tol && y < cd + 1.0 + tol) return 1;
    if ((c == 1 && y > bd * (1 - 3e-13)) || (c == b - 1 && y < 1 + 3e-13)) return 1;
    return 0;
}

// test all lanes at exponent t (state = exponent t), then advance by one
static void test_and_step(int t, int cnt, uint64_t ulimit_mode, uint64_t Bmax) {
    int64_t any = 0;
    for (int i = 0; i < cnt; i++) {
        double y = Y[i]; int64_t c = C[i], b = Bv[i]; double cd = (double)c, bd = (double)b;
        double tol = y * 3e-13 + 1e-9;
        int64_t f1 = (y >= cd - tol), f2 = (y < cd + 1.0 + tol);
        int64_t w1 = (c == 1), w2 = (y > bd * (1 - 3e-13)), w3 = (c == b - 1), w4 = (y < 1 + 3e-13);
        any |= (f1 & f2) | (w1 & w2) | (w3 & w4);
    }
    if (any) {
        for (int i = 0; i < cnt; i++) {
            uint64_t b = (uint64_t)Bv[i];
            uint64_t lim = ulimit_mode ? U[t] : Bmax;   // test b < lim   (U already includes plus1)
            if (b < lim) {
                if (lane_flag(i)) {
                    ncand++;
                    if (exact_pal(t, b)) { npal++; printf("PAL n=%d b=%llu\n", t, (unsigned long long)b); fflush(stdout); }
                }
            }
        }
    }
    steps += cnt;
    for (int i = 0; i < cnt; i++) {
        int64_t c2 = C[i] << 1, b = Bv[i]; C[i] = c2 >= b ? c2 - b : c2;
        double y2 = Y[i] * 2.0; Y[i] = y2 >= (double)b ? y2 * IB[i] : y2;
    }
}

// parity filter: must the block [B0, B1) be tested at exponent t ?
static int parity_need(int t, double lB0, double lB1, int has_mersenne) {
    if (has_mersenne) return 1;
    double v0 = (double)t * M_LN2 / lB0, v1 = (double)t * M_LN2 / lB1;
    double f0 = v0 - floor(v0), f1 = v1 - floor(v1);
    if (f0 < 1e-9 || f0 > 1 - 1e-9 || f1 < 1e-9 || f1 > 1 - 1e-9) return 1;
    long K0 = (long)floor(v0), K1 = (long)floor(v1);
    if (K0 != K1) return 1;
    return (K0 % 2) == 0;   // K even <=> odd number of digits
}

static void process_block(uint64_t B0, uint64_t B1, const int *T, int nT, int ulimit_mode, uint64_t Bmax) {
    int cnt = (int)(B1 - B0);
    int has_m = 0;
    for (int x = 2; x < 63; x++) { uint64_t m = (1ULL << x) - 1; if (m >= B0 && m < B1) has_m = 1; }
    static int L[NMAX]; int nL = 0;
    double lB0 = log((double)B0), lB1 = log((double)(B1 - 1));
    for (int j = 0; j < nT; j++) if (parity_need(T[j], lB0, lB1, has_m)) L[nL++] = T[j];
    if (nL == 0) return;
    init_state(B0, cnt, L[0]);
    int cur = L[0];
    for (int j = 0; j < nL; j++) {
        int t = L[j];
        if (t > cur) {
            if (t - cur <= GAP) { while (cur < t) { // plain steps without testing
                    for (int i = 0; i < cnt; i++) { int64_t c2 = C[i] << 1, b = Bv[i]; C[i] = c2 >= b ? c2 - b : c2;
                        double y2 = Y[i] * 2.0; Y[i] = y2 >= (double)b ? y2 * IB[i] : y2; }
                    cur++; } }
            else { advance(B0, cnt, t - cur); cur = t; }
        }
        test_and_step(t, cnt, ulimit_mode, Bmax); cur = t + 1;
    }
}

int main(int argc, char **argv) {
    if (argc < 2) return 1;
    if (strcmp(argv[1], "range") == 0) {
        int N1 = atoi(argv[2]);
        uint64_t part = strtoull(argv[3], 0, 10), nparts = strtoull(argv[4], 0, 10);
        int plus1 = (argc > 5 && strcmp(argv[5], "plus1") == 0);
        FILE *f = fopen("beta.txt", "r"); int n, be;
        while (fscanf(f, "%d %d", &n, &be) == 2) if (n < NMAX) beta[n] = be;
        fclose(f);
        uint64_t Umax = 0;
        for (n = 1; n <= N1; n++) { U[n] = (1ULL << beta[n]) - 1 + (plus1 ? 1 : 0); if (U[n] > Umax) Umax = U[n]; }
        // lists: for threshold x0, the n (sorted) with 2^beta(n) >= 2^x0
        static int lists[64][NMAX]; static int nlist[64];
        for (int x0 = 0; x0 < 64; x0++) { nlist[x0] = 0; for (n = 1; n <= N1; n++) if (beta[n] >= x0) lists[x0][nlist[x0]++] = n; }
        static int T[NMAX];
        uint64_t blockno = 0;
        for (uint64_t B0 = 3; B0 < Umax; B0 += BLK, blockno++) {
            if (blockno % nparts != part) continue;
            uint64_t B1 = B0 + BLK; if (B1 > Umax) B1 = Umax;
            int x0 = 63 - __builtin_clzll(B0);       // U[n] > B0 requires beta(n) >= floor(log2 B0)
            int nT = 0;
            for (int j = 0; j < nlist[x0]; j++) { int t = lists[x0][j]; if (U[t] > B0) T[nT++] = t; }
            if (nT) process_block(B0, B1, T, nT, 1, 0);
            if ((blockno & 0x7FFFF) == 0) { fprintf(stderr, "B0=2^%.3f steps=%.3Le inits=%lld cand=%lld pal=%lld\n", log2((double)B0), steps, ninit, ncand, npal); }
        }
        printf("DONE range N1=%d part=%llu/%llu plus1=%d steps=%.4Le inits=%lld jumps=%lld candidates=%lld palindromes=%lld\n",
               N1, (unsigned long long)part, (unsigned long long)nparts, plus1, steps, ninit, njump, ncand, npal);
    } else if (strcmp(argv[1], "upto4") == 0) {
        // test all bases b with b^4 <= 2^n (>= 5 digits), for all n <= N1 (N1 <= 250)
        int N1 = atoi(argv[2]);
        uint64_t part = strtoull(argv[3], 0, 10), nparts = strtoull(argv[4], 0, 10);
        FILE *f = fopen(argv[5], "r"); int n; unsigned long long v;   // lines: n  floor(2^(n/4))
        while (fscanf(f, "%d %llu", &n, &v) == 2) if (n <= N1) U[n] = v + 1;
        fclose(f);
        uint64_t Umax = U[N1];
        static int T[NMAX];
        uint64_t blockno = 0;
        for (uint64_t B0 = 3; B0 < Umax; B0 += BLK, blockno++) {
            if (blockno % nparts != part) continue;
            uint64_t B1 = B0 + BLK; if (B1 > Umax) B1 = Umax;
            int nT = 0;
            for (int t = 1; t <= N1; t++) if (U[t] > B0) T[nT++] = t;
            if (nT) process_block(B0, B1, T, nT, 1, 0);
            if ((blockno & 0x7FFFF) == 0) { fprintf(stderr, "B0=2^%.3f steps=%.3Le inits=%lld cand=%lld pal=%lld\n", log2((double)B0), steps, ninit, ncand, npal); }
        }
        printf("DONE upto4 N1=%d part=%llu/%llu steps=%.4Le inits=%lld jumps=%lld candidates=%lld palindromes=%lld\n",
               N1, (unsigned long long)part, (unsigned long long)nparts, steps, ninit, njump, ncand, npal);
    } else if (strcmp(argv[1], "single") == 0) {
        int n = atoi(argv[2]);
        uint64_t Bmax = strtoull(argv[3], 0, 10);
        uint64_t part = strtoull(argv[4], 0, 10), nparts = strtoull(argv[5], 0, 10);
        int T[1] = { n };
        uint64_t blockno = 0;
        for (uint64_t B0 = 3; B0 < Bmax; B0 += BLK, blockno++) {
            if (blockno % nparts != part) continue;
            uint64_t B1 = B0 + BLK; if (B1 > Bmax) B1 = Bmax;
            process_block(B0, B1, T, 1, 0, Bmax);
            if ((blockno & 0xFFFFFF) == 0) { fprintf(stderr, "n=%d B0=2^%.3f inits=%lld cand=%lld pal=%lld\n", n, log2((double)B0), ninit, ncand, npal); }
        }
        printf("DONE single n=%d Bmax=%llu part=%llu/%llu steps=%.4Le inits=%lld candidates=%lld palindromes=%lld\n",
               n, (unsigned long long)Bmax, (unsigned long long)part, (unsigned long long)nparts, steps, ninit, ncand, npal);
    }
    return 0;
}
