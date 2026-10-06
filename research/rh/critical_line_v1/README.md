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

Still open for "every zero with `0 < γ < T` lies on the line":

1. rigorous enclosures of `Λ(1/2 + it)` at sample points (ζ and Γ in interval arithmetic);
2. the zero count `N(T)` (argument principle plus the Backlund/Turing bound on `S(t)`).

This is verification up to a height, not RH. AUTHORITY_EFFECT = NONE.
