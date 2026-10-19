# writes alpha.txt: "b hi lo" with floor(2^128 * log 2 / log b) split into two 64-bit words
import mpmath
mpmath.mp.prec = 200
with open('alpha.txt', 'w') as f:
    for b in range(3, 70000):
        a = int(mpmath.floor(mpmath.mpf(2) ** 128 * mpmath.log(2) / mpmath.log(b)))
        f.write('%d %d %d\n' % (b, a >> 64, a & ((1 << 64) - 1)))
