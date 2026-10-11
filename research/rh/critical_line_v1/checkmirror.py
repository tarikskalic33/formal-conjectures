"""Exact integer mirror of the Lean checker RHLambdaCheckV1 (same rounding, same recursion order).

Iv = (lo, hi) at scale 2^-p. Every rational -> interval via floor/ceil; products via min/max corners.
  rho = (1 + 1/8)^z by the binomial series (K+1 terms) + remainder        (no log, no cos/sin)
  P_j = e^{-pi a_j}, a_j = (9/8)^j;  E_{m,j} = P_j^{m^2}                  (one exponential per boundary)
  cell (m, j):  rho^j * sum_k choose(z,k) a_j^{-k} I_k  +-  R_d I_0
  tails: e^{-alpha X}/alpha per m, three-term error <= e^{-16 pi}
"""
import sys, math
from fractions import Fraction as F

def fl(q): q = F(q); return q.numerator // q.denominator
def ce(q): q = F(q); return -((-q.numerator) // q.denominator)

class Chk:
    def __init__(s, p=128, s_sq=6, N=30, d=14, K=50, J=22, M=F(15, 2)):
        s.p, s.s, s.N, s.d, s.K, s.J, s.M = p, s_sq, N, d, K, J, M
        s.P2 = 1 << p
    # --- Iv ---
    def ofQ(s, q): q = F(q); return (fl(q * s.P2), ce(q * s.P2))
    def ball(s, q, e): return (fl((q - e) * s.P2), ce((q + e) * s.P2))
    def add(s, I, J): return (I[0] + J[0], I[1] + J[1])
    def neg(s, I): return (-I[1], -I[0])
    def sub(s, I, J): return s.add(I, s.neg(J))
    def mul(s, I, J):
        ps = [I[0] * J[0], I[0] * J[1], I[1] * J[0], I[1] * J[1]]
        return (min(ps) // s.P2, -((-max(ps)) // s.P2))
    def widen(s, I, e): return (I[0] - e, I[1] + e)
    # --- CIv ---
    def cof(s, x, y): return (s.ofQ(x), s.ofQ(y))
    def cadd(s, C, D): return (s.add(C[0], D[0]), s.add(C[1], D[1]))
    def cmul(s, C, D): return (s.sub(s.mul(C[0], D[0]), s.mul(C[1], D[1])), s.add(s.mul(C[0], D[1]), s.mul(C[1], D[0])))
    def csmul(s, I, C): return (s.mul(I, C[0]), s.mul(I, C[1]))
    def cwiden(s, C, e): return (s.widen(C[0], e), s.widen(C[1], e))
    # --- exp ---
    def taylorAux(s, x, n):
        S, T = F(0), F(1)
        for i in range(n): S, T = S + T, T * x / (i + 1)
        return S, T
    def expQ(s, x, N):
        S, _ = s.taylorAux(x, N)
        return s.ball(S, abs(x) ** N * (F(N + 1) / (math.factorial(N) * N)))
    def sqN(s, k, I):
        for _ in range(k): I = s.mul(I, I)
        return I
    def expNegQ(s, q, ss, N): return s.sqN(ss, s.expQ(-F(q) / 2 ** ss, N))
    piLo = F(314159265358979323846, 10 ** 20); piHi = F(314159265358979323847, 10 ** 20)
    def expNegPi(s, a): return (s.expNegQ(s.piHi * a, s.s, s.N)[0], s.expNegQ(s.piLo * a, s.s, s.N)[1])
    def powIv(s, I, k):
        R = s.ofQ(1)
        for _ in range(k): R = s.mul(R, I)
        return R
    # --- binomial ---
    def betaQ(s, k):
        b = F(1)
        for j in range(k): b = b * (s.M + j) / (j + 1)
        return b
    def remQ(s, d, U): return s.betaQ(d + 1) * U ** (d + 1) / (1 - U * (s.M + d + 1) / (d + 2))
    def binAux(s, zr, zi, u, k):
        S, T = s.cof(0, 0), s.cof(1, 0)
        for i in range(k):
            S, T = s.cadd(S, T), s.csmul(s.ofQ(F(u) / (i + 1)), s.cmul(T, s.cof(zr - i, zi)))
        return S, T
    def cellAux(s, zr, zi, ainv, h, invA, Eb, I0, k):
        S, T, I = s.cof(0, 0), s.cof(1, 0), I0
        for i in range(k):
            S, T, I = (s.cadd(S, s.csmul(I, T)),
                       s.csmul(s.ofQ(ainv / (i + 1)), s.cmul(T, s.cof(zr - i, zi))),
                       s.mul(s.sub(s.mul(s.ofQ(i + 1), I), s.mul(Eb, s.ofQ(h ** (i + 1)))), invA))
        return S, T, I
    def invAlpha(s, m): return (s.ofQ(1 / (s.piHi * m * m))[0], s.ofQ(1 / (s.piLo * m * m))[1])
    def lam(s, t):
        t = F(t); zr, zi = F(-3, 4), t / 2
        assert zr * zr + zi * zi <= s.M ** 2 and s.M >= 1
        assert F(1, 8) * (s.M + s.K + 1) / (s.K + 2) < 1 and F(1, 8) * (s.M + s.d + 1) / (s.d + 2) < 1
        assert s.piHi * F(9, 8) ** s.J <= 2 ** s.s
        rho = s.cwiden(s.binAux(zr, zi, F(1, 8), s.K + 1)[0], ce(s.remQ(s.K, F(1, 8)) * s.P2))
        Rd = s.remQ(s.d, F(1, 8))
        S = {m: s.cof(0, 0) for m in (1, 2, 3)}
        pw = s.cof(1, 0); P = s.expNegPi(F(1)); P0 = P
        for j in range(s.J):
            a = F(9, 8) ** j; P1 = s.expNegPi(a * F(9, 8))
            for m in (1, 2, 3):
                Ea, Eb, iA = s.powIv(P, m * m), s.powIv(P1, m * m), s.invAlpha(m)
                I0 = s.mul(s.sub(Ea, Eb), iA)
                acc = s.cellAux(zr, zi, 1 / a, a / 8, iA, Eb, I0, s.d + 1)[0]
                S[m] = s.cadd(S[m], s.cwiden(s.cmul(pw, acc), ce(Rd * I0[1])))
            pw = s.cmul(pw, rho); P = P1
        tails = sum(ce(F(s.powIv(P, m * m)[1] * s.invAlpha(m)[1], s.P2)) for m in (1, 2, 3))
        eps3 = ce(F(P0[1] ** 16, 2 ** (15 * s.p)))
        tot = s.cadd(s.cadd(S[1], S[2]), S[3])
        L = s.sub(s.widen(s.mul(s.ofQ(2), tot[0]), 2 * tails + eps3), s.ofQ(1 / (F(1, 4) + t * t)))
        return L, dict(rho=rho, Rd=float(Rd), tails=tails, eps3=eps3)

if __name__ == '__main__':
    c = Chk()
    for t in sys.argv[1:]:
        L, info = c.lam(F(t))
        lo, hi = L[0] / c.P2, L[1] / c.P2
        sg = '+' if L[0] > 0 else ('-' if L[1] < 0 else '?')
        print(f"t={t}: [{lo:.12e}, {hi:.12e}] width {hi-lo:.2e} sign {sg}  Rd={info['Rd']:.2e} tails={info['tails']} eps3={info['eps3']}")
        print(f"   lo={L[0]}\n   hi={L[1]}")
