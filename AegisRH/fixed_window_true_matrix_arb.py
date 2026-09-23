#!/usr/bin/env python3
"""Rigorous fixed-window Weil matrix evaluator for the user-supplied bridge.

This evaluates the *actual* fixed-window matrix D_N from equation (15) of
FIXED_WINDOW_BRIDGE.md, applies the exact two-moment rectangular restriction
S_N, forms K_N = R^{-1} S_N^T D_N S_N and G_N = S_N^T S_N, and certifies
K_N + eps_N G_N > 0 by interval LDL^T using Arb balls.

It deliberately does NOT identify this finite list of N values with a proof
for all N.  The output is evidence for the exact matrix formula and a reusable
input for the cofinality proof.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path

import flint
from flint import acb, arb, ctx


FORMULA_ID = "AEGIS_FIXED_WINDOW_TRUE_DN_FORMULA_15_V1"
RECEIPT_KIND = "AEGIS_FIXED_WINDOW_TRUE_MATRIX_RECEIPT_V1"


def ball_repr(x: arb, digits: int) -> dict[str, str]:
    return {
        "mid": x.mid().str(digits, radius=False),
        "rad": x.rad().str(digits, radius=False),
        "lower": x.lower().str(digits, radius=False),
        "upper": x.upper().str(digits, radius=False),
    }


def canonical_hash(obj: object) -> str:
    data = json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(data.encode("utf-8")).hexdigest()


def prime_factors(n: int) -> set[int]:
    out: set[int] = set()
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.add(d)
            while n % d == 0:
                n //= d
        d = 3 if d == 2 else d + 2
    if n > 1:
        out.add(n)
    return out


def von_mangoldt_base(n: int) -> int | None:
    fs = prime_factors(n)
    if len(fs) != 1:
        return None
    return next(iter(fs))


def prime_power_data_below(L: arb) -> list[tuple[int, int, arb, arb]]:
    """Return (q,p,log q, log p/sqrt(q)) for prime powers q with log q < L."""
    out: list[tuple[int, int, arb, arb]] = []
    q = 2
    while True:
        y = arb(q).log()
        if y > L:
            break
        if not (y < L):
            raise RuntimeError(f"PRIME_CUTOFF_UNDECIDED_AT_{q}")
        p = von_mangoldt_base(q)
        if p is not None:
            out.append((q, p, y, arb(p).log() / arb(q).sqrt()))
        q += 1
        if q > 10_000_000:
            raise RuntimeError("PRIME_CUTOFF_GUARD_EXCEEDED")
    return out


def b_k(k: int, ell: int) -> arb:
    # R = ell*pi, L = 2*ell*pi, hence b_k = k*pi/L = k/(2 ell) exactly.
    return arb(k) / arb(2 * ell)


def corr_arb(s: arb, j: int, k: int, ell: int, R: arb, L: arb) -> arb:
    bj, bk = b_k(j, ell), b_k(k, ell)
    if j == k:
        return ((L - s) * (bk * s).cos() + (bk * s).sin() / bk) / 2
    if (j + k) % 2:
        return arb(0)
    return (bj * (bk * s).sin() - bk * (bj * s).sin()) / (bj * bj - bk * bk)


def corr_acb(s: acb, j: int, k: int, ell: int, R: arb, L: arb) -> acb:
    bj, bk = acb(b_k(j, ell)), acb(b_k(k, ell))
    Lc = acb(L)
    if j == k:
        return ((Lc - s) * (bk * s).cos() + (bk * s).sin() / bk) / 2
    if (j + k) % 2:
        return acb(0)
    return (bj * (bk * s).sin() - bk * (bj * s).sin()) / (bj * bj - bk * bk)


def near_zero_error(j: int, k: int, ell: int, R: arb, eta: arb) -> arb:
    """Rigorous absolute bound for the omitted integral on [0, eta].

    Diagonal:
      R-C_jj(s) = 1/2 ||tau_s phi_j-phi_j||_2^2
                <= (R b_j^2/2) s^2.
    Off diagonal (C_jk(0)=0):
      |C_jk(s)| <= |s| ||phi'_j||_2 ||phi_k||_2
                  <= R b_j |s|,
    and symmetrically with j,k; use max(b_j,b_k).
    Since exp(s/2)/sinh(s) <= exp(eta/2)/s for 0<s<=eta.
    """
    e = (eta / 2).exp()
    bj, bk = b_k(j, ell), b_k(k, ell)
    if j == k:
        return (R * bj * bj * e * eta * eta) / 4
    if (j + k) % 2:
        return arb(0)
    bmax = bj if bj > bk else bk
    return R * bmax * e * eta


def integral_entry(j: int, k: int, ell: int, R: arb, L: arb, eta: arb, tol: arb) -> arb:
    delta = arb(1) if j == k else arb(0)

    def integrand(z: acb, analytic: bool) -> acb:
        ker = (z / 2).exp() / z.sinh()
        return ker * (acb(R * delta) - corr_acb(z, j, k, ell, R, L))

    I = acb.integral(
        integrand,
        acb(eta),
        acb(L),
        rel_tol=tol,
        abs_tol=tol,
        depth_limit=30,
        eval_limit=200_000,
    )
    if not I.is_finite():
        raise RuntimeError(f"INTEGRAL_NONFINITE_{j}_{k}")
    main = I.real
    err = near_zero_error(j, k, ell, R, eta).upper()
    return main + arb(0, err)


def tail_integral(L: arb) -> arb:
    # Exact antiderivative after x = exp(-s/2):
    # int_L^inf exp(s/2)/sinh(s) ds
    # = log((1+x)/(1-x)) + 2 atan(x), x=exp(-L/2).
    x = (-L / 2).exp()
    return ((1 + x) / (1 - x)).log() + 2 * x.atan()


def build_D(N: int, ell: int, prec_bits: int, near_zero_bits: int, tol_bits: int):
    ctx.prec = prec_bits
    pi = arb.pi()
    R = arb(ell) * pi
    L = 2 * R
    eta = arb(2) ** (-near_zero_bits)
    tol = arb(2) ** (-tol_bits)
    c_star = (8 * pi).log() + arb.const_euler() + pi / 2
    tail = tail_integral(L)
    primes = prime_power_data_below(L)

    D = [[arb(0) for _ in range(N)] for _ in range(N)]
    for a in range(N):
        j = a + 1
        for b in range(a, N):
            k = b + 1
            val = integral_entry(j, k, ell, R, L, eta, tol)
            if j == k:
                val += (tail - c_star) * R
            pterm = arb(0)
            for q, p, y, weight in primes:
                pterm += weight * corr_arb(y, j, k, ell, R, L)
            val -= 2 * pterm
            D[a][b] = val
            D[b][a] = val
    return D, R, L, eta, tail, c_star, primes


def restriction_matrix(N: int, ell: int) -> list[list[Fraction]]:
    if N < 3:
        raise ValueError("N_MUST_BE_AT_LEAST_3")
    theta = ell * ell
    cols = N - 2
    S = [[Fraction(0) for _ in range(cols)] for _ in range(N)]
    for col, k in enumerate(range(3, N + 1)):
        S[k - 1][col] = Fraction(1)
        if k % 2:
            r = Fraction(k * (1 + theta), k * k + theta)
            S[0][col] = -r
        else:
            s = Fraction(k * (4 + theta), 2 * (k * k + theta))
            S[1][col] = -s
    return S


def frac_arb(x: Fraction) -> arb:
    return arb(x.numerator) / arb(x.denominator)


def gram_exact(S: list[list[Fraction]]) -> list[list[Fraction]]:
    nrow, ncol = len(S), len(S[0])
    G = [[Fraction(0) for _ in range(ncol)] for _ in range(ncol)]
    for i in range(ncol):
        for j in range(ncol):
            G[i][j] = sum(S[r][i] * S[r][j] for r in range(nrow))
    return G


def restrict_matrix(D: list[list[arb]], S: list[list[Fraction]], scale: arb) -> list[list[arb]]:
    nrow, ncol = len(S), len(S[0])
    K = [[arb(0) for _ in range(ncol)] for _ in range(ncol)]
    for i in range(ncol):
        for j in range(i, ncol):
            acc = arb(0)
            for a in range(nrow):
                sa = frac_arb(S[a][i])
                if sa == 0:
                    continue
                for b in range(nrow):
                    sb = frac_arb(S[b][j])
                    if sb == 0:
                        continue
                    acc += sa * D[a][b] * sb
            acc /= scale
            K[i][j] = acc
            K[j][i] = acc
    return K


def interval_ldlt(A: list[list[arb]]) -> dict[str, object]:
    n = len(A)
    diag: list[arb | None] = [None] * n
    lower = [[arb(0) for _ in range(n)] for _ in range(n)]
    pivots: list[dict[str, object]] = []
    for i in range(n):
        lower[i][i] = arb(1)
        pivot = arb(A[i][i])
        for k in range(i):
            assert diag[k] is not None
            pivot -= lower[i][k] * lower[i][k] * diag[k]
        diag[i] = pivot
        if not (pivot > 0):
            pivots.append({"index": i, "positive": False, "ball": ball_repr(pivot, 80)})
            return {"positive_definite": False, "undetermined_or_nonpositive": i, "pivots": pivots}
        pivots.append({"index": i, "positive": True, "ball": ball_repr(pivot, 80)})
        for row in range(i + 1, n):
            v = arb(A[row][i])
            for k in range(i):
                assert diag[k] is not None
                v -= lower[row][k] * lower[i][k] * diag[k]
            lower[row][i] = v / pivot
    return {"positive_definite": True, "undetermined_or_nonpositive": None, "pivots": pivots}



def rational_preconditioner_from_midpoint_cholesky(
    A: list[list[arb]],
) -> list[list[Fraction]] | None:
    """Heuristic midpoint Cholesky, converted to an exact rational inverse factor.

    The floating computation has NO certificate authority.  It only chooses T.
    The returned T is exact rational and the subsequent Arb congruence/Gershgorin
    check is the actual positivity certificate.
    """
    n = len(A)
    M = [[float(A[i][j].mid()) for j in range(n)] for i in range(n)]
    L = [[0.0 for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(i + 1):
            v = M[i][j] - sum(L[i][k] * L[j][k] for k in range(j))
            if i == j:
                if not math.isfinite(v) or v <= 0.0:
                    return None
                L[i][j] = math.sqrt(v)
            else:
                if L[j][j] == 0.0:
                    return None
                L[i][j] = v / L[j][j]

    invL = [[0.0 for _ in range(n)] for _ in range(n)]
    for col in range(n):
        for i in range(n):
            rhs = 1.0 if i == col else 0.0
            rhs -= sum(L[i][k] * invL[k][col] for k in range(i))
            invL[i][col] = rhs / L[i][i]

    T = [
        [Fraction.from_float(invL[i][j]) if j <= i else Fraction(0) for j in range(n)]
        for i in range(n)
    ]
    if any(T[i][i] == 0 for i in range(n)):
        return None
    return T


def rational_congruence(
    A: list[list[arb]], Tq: list[list[Fraction]]
) -> list[list[arb]]:
    """Return the rigorous Arb enclosure of T A T^T for exact rational T."""
    n = len(A)
    T = [[frac_arb(x) for x in row] for row in Tq]
    TA = [[arb(0) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for k in range(n):
            tik = T[i][k]
            if tik == 0:
                continue
            for j in range(n):
                TA[i][j] += tik * A[k][j]

    B = [[arb(0) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            acc = arb(0)
            for k in range(n):
                tjk = T[j][k]
                if tjk != 0:
                    acc += TA[i][k] * tjk
            B[i][j] = acc
    return B


def preconditioned_gershgorin_certificate(A: list[list[arb]]) -> dict[str, object]:
    """Rigorous SPD certificate after exact rational congruence.

    If T is invertible and every Gershgorin lower margin of B=TAT^T is
    strictly positive, then B and hence A are positive definite.
    """
    Tq = rational_preconditioner_from_midpoint_cholesky(A)
    if Tq is None:
        return {
            "positive_definite": False,
            "method": "exact-rational-preconditioned-gershgorin-v1",
            "reason": "MIDPOINT_CHOLESKY_HEURISTIC_FAILED",
            "row_margins": [],
            "preconditioner_rational": None,
        }

    B = rational_congruence(A, Tq)
    margins: list[dict[str, object]] = []
    all_positive = True
    for i in range(len(B)):
        off = arb(0)
        for j in range(len(B)):
            if i != j:
                off += abs(B[i][j]).upper()
        margin = B[i][i].lower() - off
        positive = bool(margin > 0)
        all_positive = all_positive and positive
        margins.append({
            "index": i,
            "positive": positive,
            "diag": ball_repr(B[i][i], 80),
            "offdiag_abs_upper_sum": ball_repr(off, 80),
            "margin": ball_repr(margin, 80),
        })

    return {
        "positive_definite": all_positive,
        "method": "exact-rational-preconditioned-gershgorin-v1",
        "reason": None if all_positive else "NONPOSITIVE_GERSHGORIN_MARGIN",
        "row_margins": margins,
        "preconditioner_rational": [
            [f"{x.numerator}/{x.denominator}" for x in row] for row in Tq
        ],
    }


def matrix_repr(A: list[list[arb]], digits: int) -> list[list[dict[str, str]]]:
    return [[ball_repr(x, digits) for x in row] for row in A]


def run_one(N: int, ell: int, prec_bits: int, near_zero_bits: int, tol_bits: int, eps_power: int):
    D, R, L, eta, tail, c_star, primes = build_D(N, ell, prec_bits, near_zero_bits, tol_bits)
    S = restriction_matrix(N, ell)
    Gq = gram_exact(S)
    K = restrict_matrix(D, S, R)
    G = [[frac_arb(x) for x in row] for row in Gq]

    eps = Fraction(1, N ** eps_power)
    shifted = [
        [K[i][j] + frac_arb(eps) * G[i][j] for j in range(N - 2)]
        for i in range(N - 2)
    ]

    zero_ldlt = interval_ldlt(K)
    eps_ldlt = interval_ldlt(shifted)
    zero_precond = (
        {"positive_definite": True, "method": "not-needed-interval-ldlt-passed"}
        if zero_ldlt["positive_definite"]
        else preconditioned_gershgorin_certificate(K)
    )
    eps_precond = (
        {"positive_definite": True, "method": "not-needed-interval-ldlt-passed"}
        if eps_ldlt["positive_definite"]
        else preconditioned_gershgorin_certificate(shifted)
    )
    zero_verified = bool(zero_ldlt["positive_definite"] or zero_precond["positive_definite"])
    eps_verified = bool(eps_ldlt["positive_definite"] or eps_precond["positive_definite"])
    digits = max(50, int(math.ceil(prec_bits * math.log10(2))) + 8)
    receipt = {
        "receipt_kind": RECEIPT_KIND,
        "formula_id": FORMULA_ID,
        "backend": f"python-flint/{getattr(flint, '__version__', 'unknown')}",
        "prec_bits": prec_bits,
        "ell": ell,
        "R": ball_repr(R, digits),
        "L": ball_repr(L, digits),
        "N": N,
        "restricted_dimension": N - 2,
        "near_zero_eta": ball_repr(eta, digits),
        "tail_integral": ball_repr(tail, digits),
        "c_star": ball_repr(c_star, digits),
        "prime_power_count": len(primes),
        "prime_power_cutoff_last": primes[-1][0] if primes else None,
        "epsilon": {"numerator": eps.numerator, "denominator": eps.denominator, "formula": f"1/N^{eps_power}"},
        "moment_restriction_exact_rational": True,
        "gram_exact_rational": [[f"{x.numerator}/{x.denominator}" for x in row] for row in Gq],
        "unshifted_interval_ldlt": zero_ldlt,
        "unshifted_preconditioned_gershgorin": zero_precond,
        "shifted_interval_ldlt": eps_ldlt,
        "shifted_preconditioned_gershgorin": eps_precond,
        "D": matrix_repr(D, digits),
        "K": matrix_repr(K, digits),
        "claims": {
            "actual_formula_15_evaluated_with_arb": True,
            "single_N_shifted_positive_definite_verified": eps_verified,
            "single_N_unshifted_positive_definite_verified": zero_verified,
            "epsilon_formula_tends_to_zero_as_real_sequence": True,
            "all_N_certified": False,
            "fixed_window_global_nonnegativity_proven": False,
            "rh_proven": False,
        },
        "open_obligations": [
            "CERTIFY_COFINAL_INFINITE_N_FAMILY_OR_PROVE_UNIFORM_PARAMETRIC_BOUND",
            "THEN_APPLY_FIXED_WINDOW_H1_LIMIT",
            "THEN_APPLY_COFINAL_WINDOW_EXHAUSTION",
        ],
    }
    receipt["receipt_sha256"] = canonical_hash(receipt)
    return receipt


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ell", type=int, default=1)
    ap.add_argument("--Ns", default="3,4,5,6,8")
    ap.add_argument("--prec-bits", type=int, default=224)
    ap.add_argument("--near-zero-bits", type=int, default=48)
    ap.add_argument("--tol-bits", type=int, default=110)
    ap.add_argument("--epsilon-power", type=int, default=4)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()

    if args.ell <= 0:
        raise SystemExit("ELL_MUST_BE_POSITIVE")
    Ns = [int(x) for x in args.Ns.split(",") if x.strip()]
    if any(N < 3 for N in Ns):
        raise SystemExit("N_MUST_BE_AT_LEAST_3")

    results = [
        run_one(N, args.ell, args.prec_bits, args.near_zero_bits, args.tol_bits, args.epsilon_power)
        for N in Ns
    ]
    out = {
        "schema": "AEGIS_FIXED_WINDOW_TRUE_MATRIX_BATCH_V1",
        "formula_id": FORMULA_ID,
        "ell": args.ell,
        "N_values": Ns,
        "epsilon_power": args.epsilon_power,
        "all_shifted_certificates_pass": all(
            r["claims"]["single_N_shifted_positive_definite_verified"] for r in results
        ),
        "all_unshifted_interval_ldlt_pass": all(
            r["unshifted_interval_ldlt"]["positive_definite"] for r in results
        ),
        "results": results,
        "batch_claim_boundary": {
            "finite_checked_N_only": True,
            "cofinal_infinite_family_not_yet_proven": True,
            "rh_proven": False,
        },
    }
    out["batch_sha256"] = canonical_hash(out)
    path = Path(args.output)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(path)
    print(json.dumps({
        "all_shifted_certificates_pass": out["all_shifted_certificates_pass"],
        "all_unshifted_interval_ldlt_pass": out["all_unshifted_interval_ldlt_pass"],
        "batch_sha256": out["batch_sha256"],
        "results": [
            {
                "N": r["N"],
                "epsilon": r["epsilon"],
                "unshifted_ldlt_pd": r["unshifted_interval_ldlt"]["positive_definite"],
                "unshifted_verified": r["claims"]["single_N_unshifted_positive_definite_verified"],
                "shifted_ldlt_pd": r["shifted_interval_ldlt"]["positive_definite"],
                "shifted_verified": r["claims"]["single_N_shifted_positive_definite_verified"],
            }
            for r in results
        ],
    }, indent=2))


if __name__ == "__main__":
    main()
