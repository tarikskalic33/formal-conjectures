# Zeros on the critical line from sign changes (Turing, first half)

`RHCriticalLineSignV1` (Mathlib only, `[propext, Classical.choice, Quot.sound]`):

- `Xi_im`: `Λ(1/2 + it)` is real. The proof uses `completedRiemannZeta_one_sub`, `riemannZeta_conj`,
  `Gamma_conj` and `conj (1/2 + it) = 1 − (1/2 + it)`.
- `exists_zero_of_sign_change`: if `re Λ(1/2 + it)` changes sign on `[a, b]`, then `ζ(1/2 + t i) = 0`
  for some `t ∈ [a, b]`.

`RHRiemannThetaFormulaV1` (Mathlib only, standard axioms):

- `completedRiemannZeta_eq`: `Λ(s) = (𝓜A(s/2) + 𝓜A(1/2 − s/2))/2 − 1/s − 1/(1 − s)` with
  `A(x) = 1_{x>1}(θ(x) − 1)`, `θ(x) = Σ_{n∈ℤ} e^{−πn²x}` (Riemann's formula). On the line this is
  `Λ(1/2 + it) = ∫_1^∞ (θ(x) − 1) x^{−3/4} cos((t/2) log x) dx − 4/(1 + 4t²)`, with no Γ and no ζ;
  numerically it agrees with `π^{−s/2}Γ(s/2)ζ(s)` to 11 digits at t = 0, 5, 14, 14.3, 20.9, 21.1, 25, 25.1.

`RHLambdaLineV1` (imports the two above, standard axioms):

- `Xi_re_eq`: `re Λ(1/2 + it) = re 𝓜A(1/4 + it/2) − 1/(1/4 + t²)` (`A` is real, so the two Mellin
  terms are conjugate on the line).

`RHFixIntervalV1` (Mathlib only, standard axioms): fixed-point interval arithmetic, integers at
scale `2^{-p}` with outward rounding (`Iv.mem_add`, `Iv.mem_neg`, `Iv.mem_mul`), so the kernel can
evaluate enclosures with `decide`. `fixmirror.py` is the integer mirror of the full enclosure and the
spec for the Lean checker. It certifies `Λ(1/2+14i) < 0 < Λ(1/2+14.3i)`, `Λ(1/2+20.9i) > 0 > Λ(1/2+21.1i)`
and, with π to 80 digits, `Λ(1/2+24.9i) < 0`. At t ≈ 25 the 20-digit π of Mathlib is too coarse:
the cancellation amplifies its error about 10¹¹ times.

`RHThetaTailV1` (Mathlib only, standard axioms): `θ(t) − 1 = Σ_{n≥1} 2e^{−πn²t}` and, for `t ≥ 1`,
`0 ≤ θ(t) − 1 − Σ_{n=1}^{3} 2e^{−πn²t} ≤ 4e^{−16πt}` (`theta_tail_bound`).

`RHMellinThreeTermsV1` (imports the formula and the tail, standard axioms):

- `mellin_A_three_terms`: for `re w ≤ 1`,
  `‖𝓜A(w) − Σ_{n<3} 2 ∫_{x>1} x^{w−1} e^{−π(n+1)²x} dx‖ ≤ 4e^{−16π}/(16π)` (≈ 1.2·10⁻²³).

`geomirror.py` is the cell layout the kernel checker will follow. Cells are geometric, `[r^j, r^{j+1}]`
with `r = 9/8`, so the base power repeats: `a_j^{w−1} = ρ^j` with `ρ = r^{w−1}`. One `log r` and one
`e^{iθ}` are computed, and everything after that is multiplication. On each cell,
`x^{w−1} = a^{w−1} Σ_k choose(w−1, k)((x − a)/a)^k` (Mathlib `one_add_cpow_hasFPowerSeriesOnBall_zero`,
with `|x − a|/a ≤ 1/8`). The moments `∫_a^b e^{−αx}(x − a)^k dx` satisfy
`α I_k = k I_{k−1} − e^{−αb}(b − a)^k`. With 22 cells, degree 14, Q.128 and π to 20 digits the run takes
0.4 s, and the enclosures contain the Arb values:
`Λ(1/2+14i) ∈ [−2.051476, −2.051340]·10⁻⁶` (Arb: −2.0514083·10⁻⁶) and
`Λ(1/2+14.3i) ∈ [2.026476, 2.026639]·10⁻⁶` (Arb: 2.0265577·10⁻⁶).

Next: the cell expansion with its remainder, the moment recursion and the x-tail in Lean, then the
integer checker under `decide` at t = 14 and t = 14.3.

Still open for "every zero with `0 < γ < T` lies on the line":

1. rigorous enclosures of `Λ(1/2 + it)` at sample points (ζ and Γ in interval arithmetic);
2. the zero count `N(T)` (argument principle plus the Backlund/Turing bound on `S(t)`).

This is verification up to a height, not RH. AUTHORITY_EFFECT = NONE.
