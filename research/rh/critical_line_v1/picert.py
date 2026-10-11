"""Certificates for Mathlib's `pi_lower_bound` / `pi_upper_bound` at 40 digits (exact rational checks).

lower (a < pi): x_0 = 0, x_{i+1} >= sqrt(2 + x_i)  [(2b + a) d^2 <= c^2 b],  x_n <= 2 - (a / 2^(n+1))^2
upper (pi < a): x_0 = 0, x_{i+1} <= sqrt(2 + x_i)  [a^2 d <= (2d + c) b^2], x_n >= 2 - ((a - 4^-n) / 2^(n+1))^2
"""
from fractions import Fraction as F
from math import isqrt
import sys

def chain(n, P, up):
    xs, x = [], F(0)
    for _ in range(n):
        v = (2 + x) * F(4 ** P)                      # (2 + x) * 4^P, exact
        r = isqrt(v.numerator // v.denominator)
        if up:
            while F(r * r) < v: r += 1
        else:
            while F(r * r) > v: r -= 1
        y = F(r, 2 ** P)
        assert (y * y >= 2 + x) if up else (y * y <= 2 + x)
        xs.append(y); x = y
    return xs

def lower(a, n, P):
    xs = chain(n, P, True)
    assert xs[-1] <= 2 - (a / 2 ** (n + 1)) ** 2, "lower: final condition fails"
    return xs

def upper(a, n, P):
    xs = chain(n, P, False)
    assert F(1, 4 ** n) <= a
    assert xs[-1] >= 2 - ((a - F(1, 4 ** n)) / 2 ** (n + 1)) ** 2, "upper: final condition fails"
    return xs

if __name__ == '__main__':
    lo = F(31415926535897932384626433832795028841971, 10 ** 40)
    hi = F(31415926535897932384626433832795028841972, 10 ** 40)
    n, P = int(sys.argv[1]), int(sys.argv[2])
    L = lower(lo, n, P); U = upper(hi, n, P)
    print("ok", n, P, len(str(L[-1].numerator)))
