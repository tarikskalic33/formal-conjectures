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
/- Exact source declaration slice for the basis map only.
All certR data and coefficient definitions have their actual source values.
This is not a replay of unrelated analytic imports of the original modules. -/
import CertRNative
import CvSTriangularTransportV1
import CvSRealBasisBoundV1
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.Complex.Norm

open scoped BigOperators

namespace AEGIS.CvSProjectedPackedCertificateL12V1
noncomputable def rCoeff (i j : Fin 139) : ℝ :=
  (((certR.getD i.val []).getD j.val 0 : ℤ) : ℝ) / 2 ^ 40
end AEGIS.CvSProjectedPackedCertificateL12V1

namespace AEGIS.CvSSchurClosureFromBoundsV1
noncomputable def normSqCoeffs {p : ℕ} (c : Fin p → ℂ) : ℝ :=
  ∑ i, ‖c i‖ ^ 2
end AEGIS.CvSSchurClosureFromBoundsV1

namespace AEGIS.CvSProjectedSchurBridgeL12V1
open AEGIS.CvSProjectedPackedCertificateL12V1
noncomputable def R_basis (v : Fin 139 → ℂ) : Fin 139 → ℂ :=
  fun i => ∑ j : Fin 139, (rCoeff i j : ℂ) * v j

/-- Nonzero diagonal of the actual rational coefficient matrix. -/
theorem rCoeff_diag_ne_zero (i : Fin 139) : rCoeff i i ≠ 0 := by
  change (RInt i i : ℝ) / (2 : ℝ) ^ 40 ≠ 0
  apply div_ne_zero
  · exact_mod_cast certR_diag_ne_zero i
  · norm_num

/-- Surjectivity of the exact source coefficient map. -/
theorem R_basis_surjective : Function.Surjective R_basis := by
  have hu : ∀ i j : Fin 139, j < i → (rCoeff i j : ℂ) = 0 := by
    intro i j h
    have hz : rCoeff i j = 0 := by
      change (RInt i j : ℝ) / (2 : ℝ) ^ 40 = 0
      rw [certR_upper i j h]
      simp
    exact_mod_cast hz
  have hd : ∀ i : Fin 139, (rCoeff i i : ℂ) ≠ 0 := by
    intro i
    exact_mod_cast rCoeff_diag_ne_zero i
  change Function.Surjective (fun (v : Fin 139 → ℂ) (i : Fin 139) =>
    ∑ j, (rCoeff i j : ℂ) * v j)
  exact AEGIS.CvSTriangularTransportV1.upper_triangular_surjective 139 _ hu hd

/-- The actual, dimension-explicit squared Frobenius budget. -/
noncomputable def basisFrobenius : ℝ := ∑ i : Fin 139, ∑ j : Fin 139, rCoeff i j ^ 2

/-- The Frobenius budget is positive from the verified diagonal. -/
theorem basisFrobenius_pos : 0 < basisFrobenius :=
  AEGIS.CvSRealBasisBoundV1.frobenius_pos_of_entry rCoeff 0 0 (rCoeff_diag_ne_zero 0)

/-- A uniform bound for all complex source coefficient vectors. -/
theorem R_basis_normSq_bound (v : Fin 139 → ℂ) :
    (∑ i, Complex.normSq (R_basis v i)) ≤
      basisFrobenius * ∑ j, Complex.normSq (v j) := by
  simpa only [basisFrobenius, R_basis] using
    AEGIS.CvSRealBasisBoundV1.real_matrix_normSq_le rCoeff v

/-- Frobenius control in the existing CvS coefficient norm convention. -/
theorem R_basis_frobenius_bound (v : Fin 139 → ℂ) :
    AEGIS.CvSSchurClosureFromBoundsV1.normSqCoeffs (R_basis v) ≤
      basisFrobenius * AEGIS.CvSSchurClosureFromBoundsV1.normSqCoeffs v := by
  simpa only [AEGIS.CvSSchurClosureFromBoundsV1.normSqCoeffs, Complex.sq_norm] using
    R_basis_normSq_bound v

end AEGIS.CvSProjectedSchurBridgeL12V1

#print axioms AEGIS.CvSProjectedSchurBridgeL12V1.rCoeff_diag_ne_zero
#print axioms AEGIS.CvSProjectedSchurBridgeL12V1.R_basis_surjective
#print axioms AEGIS.CvSProjectedSchurBridgeL12V1.basisFrobenius_pos
#print axioms AEGIS.CvSProjectedSchurBridgeL12V1.R_basis_normSq_bound

#print axioms AEGIS.CvSProjectedSchurBridgeL12V1.R_basis_frobenius_bound
