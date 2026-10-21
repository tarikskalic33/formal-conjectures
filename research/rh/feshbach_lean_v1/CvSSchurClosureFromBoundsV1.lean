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
/-
AEGIS Ω — Schur low-block closure from coercivity and a Brow budget.
READ-ONLY source candidate. Exact source anchor cf9372f13370596d51eb36134f141f199ba60b5c.
Lean kernel compilation has NOT been performed in this environment.

Names: A_CvS is the raw CvS matrix; T_trace is a scalar trace-integral upper
bound. Neither is the invertible basis map R_basis from the projected-certificate
experiment. The bounds below apply to the *actual* lowCoeff map.
-/
import CvSRowTailV1

open Finset Complex ComplexConjugate

namespace AEGIS.CvSSchurClosureFromBoundsV1

open AEGIS.CvSLowBlockMatrixV1
open AEGIS.CvSMomentBasisV1

/-- Real entries of the underlying Fourier-frequency CvS matrix. -/
noncomputable def A_CvS (M : ℕ) (LT : ℝ) (n k : ℤ) : ℝ :=
  cvsEntry M LT n k

/-- Squared Euclidean norm of the vector of moment-atom coefficients. -/
noncomputable def normSqCoeffs {p : ℕ} (c : Fin p → ℂ) : ℝ :=
  ∑ i, ‖c i‖ ^ 2

/-- The precise finite CvS form in the `hlow` hypothesis of
    `CvSRowTailV1.window_of_certificate_tail` (NO extraneous `2*pi` factor). -/
noncomputable def Q_CvS {p : ℕ} (M : ℕ) (LT : ℝ)
    (centers : Fin p → ℤ) (c : Fin p → ℂ) : ℝ :=
  (∑ a ∈ lowFreq (fun i => sinSqSupport (centers i)),
    ∑ b ∈ lowFreq (fun i => sinSqSupport (centers i)),
      lowCoeff LT (fun i => sinSqSupport (centers i))
        (fun i => sinSqWeight (centers i)) c a *
      conj (lowCoeff LT (fun i => sinSqSupport (centers i))
        (fun i => sinSqWeight (centers i)) c b) *
      (A_CvS M LT a b : ℂ)).re

/-- Algebraic closure: Q(c) >= delta ||c||², B(c) <= beta ||c||²
    and beta <= (2pi)² LT (m - T_trace/(2pi)) delta imply the actual
    `window_of_certificate_tail.hlow` inequality. -/
theorem hlow_of_coercivity_and_budget {p : ℕ}
    (LT m T_trace delta beta : ℝ)
    (Q_form B_budget : (Fin p → ℂ) → ℝ)
    (hLT : 0 < LT)
    (hgap : 0 < m - T_trace / (2 * Real.pi))
    (hQ : ∀ c, delta * normSqCoeffs c ≤ Q_form c)
    (hB : ∀ c, B_budget c ≤ beta * normSqCoeffs c)
    (hbeta : beta ≤ (2 * Real.pi) ^ 2 * LT *
       (m - T_trace / (2 * Real.pi)) * delta) :
    ∀ c, B_budget c / (2 * Real.pi * LT) /
      (m - T_trace / (2 * Real.pi)) ≤ 2 * Real.pi * Q_form c := by
  intro c
  have hnorm : 0 ≤ normSqCoeffs c := by
    unfold normSqCoeffs
    exact Finset.sum_nonneg (fun i _ => sq_nonneg (‖c i‖))
  have hscale : 0 ≤ (2 * Real.pi) ^ 2 * LT *
      (m - T_trace / (2 * Real.pi)) := by positivity
  have hden : 0 < 2 * Real.pi * LT := by positivity
  have hBmajor : B_budget c ≤
      (2 * Real.pi) ^ 2 * LT * (m - T_trace / (2 * Real.pi)) * Q_form c := by
    calc
      B_budget c ≤ beta * normSqCoeffs c := hB c
      _ ≤ ((2 * Real.pi) ^ 2 * LT *
        (m - T_trace / (2 * Real.pi)) * delta) * normSqCoeffs c :=
          mul_le_mul_of_nonneg_right hbeta hnorm
      _ = ((2 * Real.pi) ^ 2 * LT *
        (m - T_trace / (2 * Real.pi))) * (delta * normSqCoeffs c) := by ring
      _ ≤ ((2 * Real.pi) ^ 2 * LT *
        (m - T_trace / (2 * Real.pi))) * Q_form c :=
          mul_le_mul_of_nonneg_left (hQ c) hscale
  apply (div_le_iff₀ hgap).2
  apply (div_le_iff₀ hden).2
  calc
    B_budget c ≤ (2 * Real.pi) ^ 2 * LT *
      (m - T_trace / (2 * Real.pi)) * Q_form c := hBmajor
    _ = (2 * Real.pi * Q_form c *
      (m - T_trace / (2 * Real.pi))) * (2 * Real.pi * LT) := by ring

/-- Specialized bridge matching the `hlow` expression of
    `CvSRowTailV1.window_of_certificate_tail` definitionally. -/
theorem cvs_hlow_of_coercivity_and_budget {p : ℕ}
    (M : ℕ) (LT m T_trace delta beta : ℝ)
    (centers : Fin p → ℤ) (Brow : (Fin p → ℂ) → ℝ)
    (hLT : 0 < LT)
    (hgap : 0 < m - T_trace / (2 * Real.pi))
    (hQ : ∀ c, delta * normSqCoeffs c ≤ Q_CvS M LT centers c)
    (hB : ∀ c, Brow c ≤ beta * normSqCoeffs c)
    (hbeta : beta ≤ (2 * Real.pi) ^ 2 * LT *
      (m - T_trace / (2 * Real.pi)) * delta) :
    ∀ c, Brow c / (2 * Real.pi * LT) /
      (m - T_trace / (2 * Real.pi)) ≤
      2 * Real.pi *
        (∑ a ∈ lowFreq (fun i => sinSqSupport (centers i)),
          ∑ b ∈ lowFreq (fun i => sinSqSupport (centers i)),
            lowCoeff LT (fun i => sinSqSupport (centers i))
              (fun i => sinSqWeight (centers i)) c a *
            conj (lowCoeff LT (fun i => sinSqSupport (centers i))
              (fun i => sinSqWeight (centers i)) c b) *
            (cvsEntry M LT a b : ℂ)).re := by
  intro c
  exact hlow_of_coercivity_and_budget LT m T_trace delta beta
    (Q_CvS M LT centers) Brow hLT hgap hQ hB hbeta c

end AEGIS.CvSSchurClosureFromBoundsV1

#print axioms AEGIS.CvSSchurClosureFromBoundsV1.hlow_of_coercivity_and_budget
#print axioms AEGIS.CvSSchurClosureFromBoundsV1.cvs_hlow_of_coercivity_and_budget
