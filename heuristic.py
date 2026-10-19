# Random-digit model: expected number of counterexamples to b(2^n) = 2^beta(n) - 1 (Section 12).
# For each n, sum b^{-(D-1)/2} over bases 3 <= b <= 2^beta(n) - 2 in which 2^n has an odd number D of digits.
import numpy as np
B = [0]*1501
for l in open('beta.txt'):
    n_, b_ = map(int, l.split()); B[n_] = b_
from math import log2, log, ceil, floor
def log2add(a, b):
    if a == -np.inf: return b
    if b == -np.inf: return a
    m = max(a,b); return m + log2(2**(a-m) + 2**(b-m))
def logE(n):
    lBm = log2(2**int(B[n]) - 2)   # largest base tested is 2^beta - 2
    tot = -np.inf
    D = max(2, int(n / lBm))
    while True:
        lL = n / D; lU = n / (D-1)
        llo = max(lL, log2(3)); lhi = min(lU, lBm)
        if D % 2 == 1 and lhi > llo:
            s = (D-1)/2
            if s == 1: t = log2(log(2)*(lhi-llo))
            else:
                # integral_{lo}^{hi} b^-s db = (lo^{1-s} - hi^{1-s})/(s-1)
                t = (1-s)*llo + log2(1 - 2**((1-s)*(lhi-llo))) - log2(s-1)
            tot = log2add(tot, t)
        if lL < log2(3): break
        D += 1
    return tot
s64 = -np.inf
for n in range(65, 600): s64 = log2add(s64, logE(n))
s1000 = -np.inf
for n in range(1001, 1400): s1000 = log2add(s1000, logE(n))
print('sum_{n>64}  E(n) ~ 2^%.2f = %.3g' % (s64, 2**s64))
print('sum_{n>1000} E(n) ~ 2^%.2f' % s1000)
print('log2 E(n) for n=65..70:', [round(logE(n),2) for n in range(65,71)])
print('log2 E(n) for n=1001..1005:', [round(logE(n),2) for n in range(1001,1006)])
