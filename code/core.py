from math import comb, isqrt
import gmpy2
from gmpy2 import mpz

def digits(N, b):
    N = mpz(N); d = []
    while N:
        N, r = gmpy2.f_divmod(N, b); d.append(int(r))
    return d  # little-endian

def is_pal(N, b):
    d = digits(N, b); return d == d[::-1]

def binom_ok(n, x):
    """2^n has binomial form in base 2^x-1 (x>=2)."""
    b = (1 << x) - 1
    k, r = divmod(n, x)
    return (1 << r) * comb(k, (k + 1) // 2) < b

def beta(n):
    x = 2
    while not binom_ok(n, x): x += 1
    return x

def bmin(n, limit=None):
    """exact smallest palindromic base by brute force up to limit"""
    N = mpz(1) << n
    b = 2
    while True:
        if limit and b > limit: return None
        if is_pal(N, b): return b
        b += 1
