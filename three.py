# non-binomial representations 2^n = (1,c,1)_b  <=>  2^n - 1 = b*k with b <= k <= 2b-1, b != 2^(n/2)-1
from sympy import factorint, divisors, cyclotomic_poly
from sympy.ntheory import factorint
from math import isqrt
import sys, signal
def fac_mersenne(n):
    f = {}
    for d in divisors(n):
        v = int(cyclotomic_poly(d, 2))
        for p, e in factorint(v).items(): f[p] = f.get(p, 0) + e
    return f
def divs_from(f):
    ds = [1]
    for p, e in f.items():
        ds = [d * p**i for d in ds for i in range(e + 1)]
    return ds
res = {}
for n in range(3, int(sys.argv[1]) + 1):
    N = (1 << n) - 1
    f = fac_mersenne(n)
    sols = []
    for b in divs_from(f):
        k = N // b
        if b <= k <= 2 * b - 1 and not (n % 2 == 0 and b == (1 << (n // 2)) - 1) and b >= 2:
            sols.append(b)
    res[n] = sorted(sols)
    print(n, len(sols), sols[:3], flush=True)
