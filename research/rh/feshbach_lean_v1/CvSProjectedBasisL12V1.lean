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

import CvSTriangularTransportV1
import CvSRealBasisBoundV1
import CvSProjectedTransportL12V1
import CvSProjectedEntryL12V1

/-!
# Exact source basis control for the fixed 139-atom CvS certificate

Back substitution proves surjectivity of the actual rational basis map.
Cauchy-Schwarz gives its squared Frobenius norm bound. These discharge
`hRsurj` and `hRnorm` in the existing consumers without changing certificate data.
The closed entry check and the Schur budget remain explicit premises.
-/

open scoped BigOperators
namespace AEGIS.CvSProjectedBasisL12V1
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open AEGIS.CvSProjectedPackedCertificateL12V1
open AEGIS.CvSProjectedSchurBridgeL12V1
open AEGIS.CvSSchurClosureFromBoundsV1
open AEGIS.CvSPackedGramV1
open AEGIS.CvSMomentBasisV1

/-- Integer numerator of the unchanged source change of basis. -/
def RInt (i j : Fin 139) : ℤ := (certR.getD i.val []).getD j.val 0

/-- The stored coefficient matrix is upper triangular. -/
theorem certR_upper : ∀ i j : Fin 139, j < i → RInt i j = 0 := by
  decide +kernel

/-- Every stored diagonal numerator is nonzero. -/
theorem certR_diag_ne_zero : ∀ i : Fin 139, RInt i i ≠ 0 := by
  decide +kernel

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

/-- Actual CvS coercivity with the source basis obligations discharged.
The actual entry enclosure remains an explicit premise. -/
theorem original_atom_coercivity_of_basis (M : ℕ)
    (hIv : ∀ i j : Fin 139,
      (Im certI i.val j.val).Mem certQ (projectedEntry M i j)) :
    ∀ c, (certifiedMu / basisFrobenius) * normSqCoeffs c ≤
      Q_CvS M (6 / 5) atomCenter c := by
  exact AEGIS.CvSProjectedTransportL12V1.original_atom_coercivity_of_transport
    M basisFrobenius basisFrobenius_pos hIv R_basis_surjective R_basis_frobenius_bound

/-- At the fixed window, only the finite entry check remains for source coercivity. -/
theorem original_atom_coercivity_of_checked_source
    [Fact (AEGIS.CvSProjectedEntryL12V1.bigCheck = true)] (M : ℕ) (hM : 3 ≤ M) :
    ∀ c, (certifiedMu / basisFrobenius) * normSqCoeffs c ≤
      Q_CvS M (6 / 5) atomCenter c := by
  exact original_atom_coercivity_of_basis M
    (AEGIS.CvSProjectedEntryL12V1.projectedEntry_mem_certI_of_check hM)

/-- The existing low-block consumer with basis and transport obligations discharged.
The finite entry check, row budget and scalar Schur gap remain explicit. -/
theorem hlow_of_checked_source
    [Fact (AEGIS.CvSProjectedEntryL12V1.bigCheck = true)] (M : ℕ) (hM : 3 ≤ M)
    (m T_trace beta : ℝ) (Brow : (Fin 139 → ℂ) → ℝ)
    (hgap : 0 < m - T_trace / (2 * Real.pi))
    (hBrow : ∀ c, Brow c ≤ beta * normSqCoeffs c)
    (hbeta : beta ≤ (2 * Real.pi) ^ 2 * (6 / 5 : ℝ) *
      (m - T_trace / (2 * Real.pi)) * (certifiedMu / basisFrobenius)) :
    ∀ c, Brow c / (2 * Real.pi * (6 / 5 : ℝ)) /
      (m - T_trace / (2 * Real.pi)) ≤
      2 * Real.pi * Q_CvS M (6 / 5) atomCenter c := by
  exact AEGIS.CvSProjectedTransportL12V1.hlow_of_projected_packed_of_transport
    M m T_trace beta basisFrobenius Brow basisFrobenius_pos hgap
    (AEGIS.CvSProjectedEntryL12V1.projectedEntry_mem_certI_of_check hM)
    R_basis_surjective R_basis_frobenius_bound hBrow hbeta

end AEGIS.CvSProjectedBasisL12V1

#print axioms AEGIS.CvSProjectedBasisL12V1.certR_upper
#print axioms AEGIS.CvSProjectedBasisL12V1.certR_diag_ne_zero
#print axioms AEGIS.CvSProjectedBasisL12V1.rCoeff_diag_ne_zero
#print axioms AEGIS.CvSProjectedBasisL12V1.R_basis_surjective
#print axioms AEGIS.CvSProjectedBasisL12V1.basisFrobenius_pos
#print axioms AEGIS.CvSProjectedBasisL12V1.R_basis_normSq_bound
#print axioms AEGIS.CvSProjectedBasisL12V1.R_basis_frobenius_bound
#print axioms AEGIS.CvSProjectedBasisL12V1.original_atom_coercivity_of_basis
#print axioms AEGIS.CvSProjectedBasisL12V1.original_atom_coercivity_of_checked_source
#print axioms AEGIS.CvSProjectedBasisL12V1.hlow_of_checked_source
