# Zeros on the critical line from sign changes (Turing, first half)

**Three zeros of ζ on the critical line, kernel-checked** (axioms `[propext, Classical.choice, Quot.sound]`):

- `RHFirstZeroV1.first_zero`: `∃ t ∈ [14, 14.3], ζ(1/2 + it) = 0`;
- `RHSecondZeroV1.second_zero`: `∃ t ∈ [20.9, 21.1], ζ(1/2 + it) = 0`;
- `RHThirdZeroV1.third_zero`: `∃ t ∈ [24.9, 25.1], ζ(1/2 + it) = 0`; `three_zeros` puts them together.

Numerically these are the zeros at t ≈ 14.1347, 21.0220 and 25.0109. The Lean statements are only that
some zero lies on the line in each window (no claim that nothing else lies there or below). They come
from sign changes of `re Λ(1/2 + it)`. They do not say every zero is on the line (that is RH).

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

`RHCellBinomialV1` (Mathlib only, standard axioms):

- `choose_succ`: `choose(z, k+1) = choose(z, k)(z − k)/(k + 1)`.
- `binom_hasSum`: `(1 + u)^z = Σ_k choose(z, k) u^k` for real `|u| < 1` (from
  `one_add_cpow_hasFPowerSeriesOnBall_zero`).
- `binom_rem_le`: for `0 ≤ u ≤ U`, `‖z‖ ≤ M`, `1 ≤ M`, `q = U(M + d + 1)/(d + 2) < 1`,
  `‖(1 + u)^z − Σ_{k≤d} choose(z, k) u^k‖ ≤ β_{d+1} U^{d+1}/(1 − q)` with `β_k = Π_{j<k}(M + j)/(j + 1)`.
- `cpow_cell`: `x^z = a^z (1 + (x − a)/a)^z` for `0 < a ≤ x`. `cpow_geom`: `(r^j)^z = (r^z)^j`.

`RHCellMomentsV1` (imports the above, standard axioms):

- `mom_zero`, `mom_succ`: `α I_0 = e^{−αa} − e^{−αb}` and `α I_{k+1} = (k + 1) I_k − e^{−αb}(b − a)^{k+1}`
  for `I_k = ∫_a^b e^{−αx}(x − a)^k dx`.
- `cell_approx`: for `1 ≤ a ≤ b`, `re z ≤ 0`, `(b − a)/a ≤ U`,
  `‖∫_a^b x^z e^{−αx} dx − a^z Σ_{k≤d} choose(z, k) a^{−k} I_k‖ ≤ β_{d+1} U^{d+1}/(1 − q) · I_0`.

`RHPi40V1` (Mathlib only, standard axioms): `π` to forty digits (`pi_gt_d40`, `pi_lt_d40`) by Mathlib's
`sqrtTwoAddSeries` chain, 72 steps at `2^{-290}`. The tactic `pi_bound_pow2` computes the witnesses
(`⌈√·⌉` / `⌊√·⌋` on naturals) and `norm_num` checks every step, so the generator is untrusted; `picert.py`
is its exact mirror. Compiles in about 15 s.

`RHExpEnclosureV1` (standard axioms): `ofQ`/`ball` (rational to integer interval), `e^x` from
`Real.exp_bound`, `e^{−q} = (e^{−q/2^s})^{2^s}`, `e^{−πa}` from `π` to forty digits (`RHPi40V1`), and
`e^{−πm²a} = (e^{−πa})^{m²}` (`exp_neg_pi_sq`), so one exponential serves `m = 1, 2, 3`.

`RHLambdaCheckV1`: the integer checker `lamIv` (complex intervals, `binAux` for `ρ = (9/8)^z`, `cellAux`
for the coefficients and the moments together, `loopJ` over the 22 cells). `checkmirror.py` is its
operation-for-operation mirror; `#eval` in Lean and the mirror give the same integers.

`RHCheckSoundV1`, `RHCheckLoopV1` (standard axioms): every operation encloses its real or complex value
(`binAux_mem`, `cellAux_mem`, `cellV_mem`, `loopJ_mem`).

`RHCellSplitV1` (standard axioms): `∫_{x>1} = Σ_{j<J} ∫_{a_j}^{a_{j+1}} + ∫_{x>a_J}` and
`‖∫_{x>X} x^z e^{−αx}‖ ≤ e^{−αX}/α`.

`RHFirstZeroV1` (standard axioms):

- `lamIv_mem`: `re Λ(1/2 + it) ∈ lamIv p t M d K J s N` whenever `1 ≤ M`, `9/16 + t²/4 ≤ M²`,
  `(M + K + 1)/(8(K + 2)) < 1`, `(M + d + 1)/(8(d + 2)) < 1`, `π_hi (9/8)^J ≤ 2^s`, `0 < N`.
- `lam14_neg`, `lam143_pos` (`decide +kernel`, about two minutes each): at `p = 128`, `d = 14`, `K = 50`,
  `J = 22`, `s = 6`, `N = 30`, `M = 15/2`:
  `re Λ(1/2 + 14i) ∈ [−2.051501, −2.051316]·10⁻⁶` and `re Λ(1/2 + 14.3i) ∈ [2.026465, 2.026650]·10⁻⁶`
  (Arb: −2.0514083·10⁻⁶ and 2.0265577·10⁻⁶).
- `first_zero`: the sign change gives `ζ(1/2 + it) = 0` for some `t ∈ [14, 14.3]`.

CI: `.github/workflows/rh-critical-line-v1.yml` compiles all of these in order against plain Mathlib
(the pin in `lake-manifest.json`, no other repositories) and fails unless every `#print axioms` report
is within `[propext, Classical.choice, Quot.sound]` and `first_zero`, `two_zeros`, `three_zeros` are
reported.

`RHSecondZeroV1` (standard axioms): the same `lamIv_mem` with `M = 11`, `d = 18`, `K = 60`;
`lam209_pos`, `lam211_neg` (`decide +kernel`): `re Λ(1/2 + 20.9i) ∈ [1.085337, 1.086279]·10⁻⁸` and
`re Λ(1/2 + 21.1i) ∈ [−5.859899, −5.850487]·10⁻⁹` (Arb: 1.0858080·10⁻⁸ and −5.8551929·10⁻⁹);
`second_zero`, `two_zeros`.

`RHThirdZeroV1` (standard axioms): `M = 13`, `d = 22`, `K = 70`; `lam249_neg`, `lam251_pos`:
`re Λ(1/2 + 24.9i) ∈ [−4.82157, −4.82061]·10⁻¹⁰` and `re Λ(1/2 + 25.1i) ∈ [3.39414, 3.39510]·10⁻¹⁰`
(Arb: −4.8210895·10⁻¹⁰ and 3.3946199·10⁻¹⁰); `third_zero`, `three_zeros`. This needed the forty
digits: with twenty, the relative error 3·10⁻²¹ of `π` enters `I_0` through `1/α` and the forward moment
recursion multiplies it by about `k!/α^k`, so the enclosure at t = 24.9 was too wide to give a sign.

Kernel times on one core: about 4.5, 4.5 and 7 minutes for the three pairs of checks.

Next: more zeros (t ≈ 30.42, 32.94, 37.59, ...) with the same checker, then the zero count `N(T)`.

Still open for "every zero with `0 < γ < T` lies on the line":

1. enclosures of `Λ(1/2 + it)` at sample points: done at t = 14, 14.3, 20.9, 21.1, 24.9, 25.1 (`lamIv`),
   without ζ or Γ;
2. the zero count `N(T)` (argument principle plus the Backlund/Turing bound on `S(t)`).

This is verification up to a height, not RH. AUTHORITY_EFFECT = NONE.
