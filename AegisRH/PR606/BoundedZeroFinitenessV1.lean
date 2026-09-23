/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
AEGIS Ω — pinned bounded Riemann-zeta zero finiteness bridge v1.

At the pinned Mathlib revision used by the Formal Conjectures RH target,
`Mathlib.NumberTheory.LSeries.ZetaZeros` already proves that the Riemann-zeta
zero set is discrete and that its intersection with every compact set is finite.

This file does not re-prove that analytic theorem. It binds the upstream
machine-checked result to the AEGIS zero-side interface with an exact set
equivalence, preserving the stronger upstream scope.

UPSTREAM_BOUNDED_ZERO_FINITE_SUPPORT
GLOBAL_ZERO_ENUMERATION_OPEN
GLOBAL_ZERO_SUM_OPEN
EXPLICIT_FORMULA_THEOREM_OPEN
-/

open Set
open Complex

noncomputable section

/-- Riemann-zeta zeros lying in a declared region `K`, in the AEGIS interface shape. -/
def RiemannZeroSetOnV1 (K : Set ℂ) : Set ℂ :=
  { z | z ∈ K ∧ riemannZeta z = 0 }

/-- The AEGIS regional zero set is definitionally equivalent to intersection
    with Mathlib's canonical `riemannZetaZeros` set. -/
theorem riemann_zero_set_eq_mathlib_inter_v1 (K : Set ℂ) :
    RiemannZeroSetOnV1 K = K ∩ riemannZetaZeros := by
  ext z
  simp [RiemannZeroSetOnV1, mem_riemannZetaZeros]

/-- Every compact region contains only finitely many Riemann-zeta zeros.
    This is a direct bridge to Mathlib's pinned theorem
    `IsCompact.inter_riemannZetaZeros_finite`. -/
theorem riemann_zero_set_finite_on_compact_v1
    {K : Set ℂ} (hK : IsCompact K) :
    (RiemannZeroSetOnV1 K).Finite := by
  rw [riemann_zero_set_eq_mathlib_inter_v1]
  exact hK.inter_riemannZetaZeros_finite

#check riemannZetaZeros
#check mem_riemannZetaZeros
#check isDiscrete_riemannZetaZeros
#check IsCompact.inter_riemannZetaZeros_finite
#check riemann_zero_set_eq_mathlib_inter_v1
#check riemann_zero_set_finite_on_compact_v1

#print axioms riemann_zero_set_eq_mathlib_inter_v1
#print axioms riemann_zero_set_finite_on_compact_v1
