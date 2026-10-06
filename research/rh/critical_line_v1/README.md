# Zeros on the critical line from sign changes (Turing, first half)

`RHCriticalLineSignV1` (Mathlib only, `[propext, Classical.choice, Quot.sound]`):

- `Xi_im`: `Λ(1/2 + it)` is real. The proof uses `completedRiemannZeta_one_sub`, `riemannZeta_conj`,
  `Gamma_conj` and `conj (1/2 + it) = 1 − (1/2 + it)`.
- `exists_zero_of_sign_change`: if `re Λ(1/2 + it)` changes sign on `[a, b]`, then `ζ(1/2 + t i) = 0`
  for some `t ∈ [a, b]`.

Still open for "every zero with `0 < γ < T` lies on the line":

1. rigorous enclosures of `Λ(1/2 + it)` at sample points (ζ and Γ in interval arithmetic);
2. the zero count `N(T)` (argument principle plus the Backlund/Turing bound on `S(t)`).

This is verification up to a height, not RH. AUTHORITY_EFFECT = NONE.
