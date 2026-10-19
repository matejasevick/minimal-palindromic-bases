# longest run of matching outer digit pairs of 2^n in base b ("near-palindromes"), n <= N
import gmpy2, sys, math
N = int(sys.argv[1])
for b in [3, 5, 6, 7, 10]:
    best = (0, 0); cnt = {}
    x = gmpy2.mpz(1)
    for n in range(1, N + 1):
        x <<= 1
        if n < 40: continue
        s = gmpy2.digits(x, b)
        L = len(s); j = 0
        while j < L // 2 and s[j] == s[L - 1 - j]: j += 1
        cnt[j] = cnt.get(j, 0) + 1
        if j > best[0]: best = (j, n)
    tail = {j: sum(v for k, v in cnt.items() if k >= j) for j in range(1, best[0] + 1)}
    pred = {j: round((N - 39) * b ** (-j), 1) for j in range(1, best[0] + 1)}
    print(f"base {b}: longest match {best[0]} outer pairs (n={best[1]}); "
          f"#n with >=j matches vs random model N*b^-j:", {j: (tail[j], pred[j]) for j in range(1, best[0] + 1)})
