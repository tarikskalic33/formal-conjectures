"""Geometric cells [r^j, r^{j+1}]: the base power repeats, a_j^{w-1} = rho^j with rho = r^{w-1}.

  G_n(w) = int_1^inf x^{w-1} e^{-alpha x} dx,  alpha = pi n^2,
  on a cell [a, ra]:  x^{w-1} = a^{w-1} sum_k choose(w-1,k) ((x-a)/a)^k   (|x-a|/a <= r-1 < 1)
  I_k = int_a^b e^{-alpha x}(x-a)^k dx :  alpha I_k = k I_{k-1} - e^{-alpha b} h^k  (k>=1),  alpha I_0 = e^{-alpha a} - e^{-alpha b}
One log (log r), one e^{i theta}, then only multiplications.
"""
import sys, math
from fractions import Fraction as Fr
sys.path.insert(0, __import__('os').path.dirname(__file__))
from fixmirror import I, C, PI, ONE, P, exp_, log_, cos_sin, err_units

def choose_abs_tail(wr, wi, d, u):
    """sum_{k>d} |choose(w-1,k)| u^k, bounded by first term / (1 - q), q >= |w-1-k| u/(k+1) for k > d."""
    m = math.sqrt(float(wr*wr + wi*wi)) * (1 + 1e-12)
    b = 1.0
    for j in range(d + 1): b *= (m + j) / (j + 1)
    q = (m + d + 1) / (d + 2) * float(u)
    assert q < 1
    return Fr(b * float(u) ** (d + 1) / (1 - q)) * Fr(1001, 1000)

def lam(t, r=Fr(9, 8), J=22, d=14, nmax=3):
    t = Fr(t); wr, wi = Fr(-3, 4), t / 2                    # w - 1
    lr = log_(r)                                             # the one log
    cr, sr = cos_sin(lr * wi); mag = exp_(lr * wr)
    rho = C(mag * cr, mag * sr)                              # r^{w-1}
    total = C(I.of(0), I.of(0)); rem = Fr(0)
    pw = C(I.of(1), I.of(0)); a = Fr(1)
    tailc = choose_abs_tail(wr, wi, d, r - 1)
    for j in range(J):
        b = a * r; h = b - a
        coef = []; ch = C(I.of(1), I.of(0))                    # choose(w-1,k) / a^k
        for k in range(d + 1):
            coef.append(pw * ch)
            ch = ch * C(I.of(wr - k), I.of(wi)) * I.of(Fr(1, (k + 1)) / a)
        for n in range(1, nmax + 1):
            al = PI * (n * n)
            ea, eb = exp_(-al * a), exp_(-al * b)
            Ik = (ea - eb) / al; acc = coef[0] * Ik
            hk = Fr(1)
            for k in range(1, d + 1):
                hk *= h
                Ik = (Ik * I.of(k) - eb * I.of(hk)) / al
                acc = acc + coef[k] * Ik
            total = total + acc * I.of(2)
            rem += 2 * tailc * Fr(ea.hi, ONE) * h                # |a^{w-1}| <= 1, int_a^b e^{-al x} <= h e^{-al a}
        pw = pw * rho; a = b
    X = a
    tail_n = Fr(2) * Fr(exp_(-(PI * 16)).hi, ONE) * 2 / 16 / 3   # n > 3 (three-term module): 4 e^{-16 pi}/(16 pi)
    tail_x = sum(2 * Fr(exp_(-(PI * (n * n)) * X).hi, ONE) / (3 * n * n) for n in range(1, nmax + 1))
    E = rem + tail_n + tail_x
    val = total.re - I.of(1 / (Fr(1, 4) + t * t))
    return val.widen(err_units(E)), E, float(X)

if __name__ == '__main__':
    for t in sys.argv[1:]:
        v, E, X = lam(Fr(t))
        lo, hi = v.f()
        s = '+' if v.lo > 0 else ('-' if v.hi < 0 else '?')
        print(f't={t}: [{lo:.12e}, {hi:.12e}] width {hi-lo:.1e} analytic {float(E):.1e} X={X:.2f} sign {s}', flush=True)
