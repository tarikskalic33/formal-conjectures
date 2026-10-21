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
AEGIS Ω — source-locked actual CvS cross-row identification.
No interval membership, new axiom, or claim of unconditional RH.
The existing source imports and signed-frequency bijection are reused.
-/
import CvSProjectedTransportL12V1
import CvSRowTailV1

open scoped BigOperators ComplexConjugate
open Finset

namespace AEGIS.CvSActualCrossRowL12V1

open AEGIS.CvSMomentBasisV1
open AEGIS.CvSLowBlockMatrixV1
open AEGIS.CvSCrossCertV1
open AEGIS.CvSRowTailV1
open AEGIS.CvSProjectedPackedCertificateL12V1
open AEGIS.CvSProjectedSchurBridgeL12V1
open AEGIS.CvSProjectedTransportL12V1

/-- The real CvS cross-row kernel used by the Q96 generator.
Both source entries are kept explicitly; symmetry is proved independently. -/
noncomputable def sourceKernel (M : ℕ) (m n : ℤ) : ℝ :=
  Real.pi * (cvsEntry M (6 / 5) n m + cvsEntry M (6 / 5) m n)

/-- Exact diagonal, matching the generator's `2*pi*diag` rule. -/
theorem sourceKernel_diag (M : ℕ) (n : ℤ) :
    sourceKernel M n n = 2 * Real.pi * cvsEntry M (6 / 5) n n := by
  unfold sourceKernel
  ring

/-- Exact divided difference on unequal frequency indices, matching
the generator's `(L/pi)*(tau_n-tau_m)/(n-m)` rule. -/
theorem sourceKernel_off (M : ℕ) (m n : ℤ) (hnm : n ≠ m) :
    sourceKernel M m n =
      ((6 / 5 : ℝ) / Real.pi) *
        ((tau M (6 / 5) n - tau M (6 / 5) m) / ((n : ℝ) - m)) := by
  unfold sourceKernel
  rw [show cvsEntry M (6 / 5) m n = cvsEntry M (6 / 5) n m from
    (cvsEntry_symm M (by norm_num : (0 : ℝ) < 6 / 5) m n)]
  rw [cvsEntry_off M (by norm_num : (0 : ℝ) < 6 / 5) hnm]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hnmR : ((n : ℝ) - m) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnm)
  field_simp
  ring

/-- The source-locked real coefficient of the cross row Y_m.
No floating approximation and no reconstruction of the existing X table. -/
noncomputable def sourceY (M : ℕ) (m : ℤ) (i : Fin 139) : ℝ :=
  ∑ k : Fin 141, transformedCoeff k i * sourceKernel M m (signedFreq k)

/-- The actual source crossRow on R_basis(v) is precisely Y*v. -/
theorem sourceY_eq_actual_crossRow (M : ℕ) (m : ℤ) (v : Fin 139 → ℂ) :
    (∑ i : Fin 139, (sourceY M m i : ℂ) * v i) =
      crossRow M (6 / 5)
        (lowFreq (fun i : Fin 139 => sinSqSupport (atomCenter i)))
        (lowCoeff (6 / 5) (fun i : Fin 139 => sinSqSupport (atomCenter i))
          (fun i => sinSqWeight (atomCenter i)) (R_basis v)) m := by
  let F : Finset ℤ := lowFreq (fun i : Fin 139 => sinSqSupport (atomCenter i))
  let a : ℤ → ℂ := lowCoeff (6 / 5)
    (fun i : Fin 139 => sinSqSupport (atomCenter i))
    (fun i => sinSqWeight (atomCenter i)) (R_basis v)
  have ha (k : Fin 141) :
      (∑ i : Fin 139, (transformedCoeff k i : ℂ) * v i) =
        a (signedFreq k) := by
    exact transformed_coeff_eq_lowCoeff v k
  change (∑ i : Fin 139, (sourceY M m i : ℂ) * v i) =
    crossRow M (6 / 5) F a m
  calc
    _ = ∑ i : Fin 139, ∑ k : Fin 141,
        ((transformedCoeff k i : ℂ) *
          (sourceKernel M m (signedFreq k) : ℂ)) * v i := by
          simp only [sourceY, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
    _ = ∑ k : Fin 141, ∑ i : Fin 139,
        ((transformedCoeff k i : ℂ) * v i) *
          (sourceKernel M m (signedFreq k) : ℂ) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ =>
            Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ k : Fin 141,
        (∑ i : Fin 139, (transformedCoeff k i : ℂ) * v i) *
          (sourceKernel M m (signedFreq k) : ℂ) := by
          simp only [Finset.sum_mul]
    _ = ∑ k : Fin 141,
        a (signedFreq k) * (sourceKernel M m (signedFreq k) : ℂ) :=
          Finset.sum_congr rfl fun k _ => by rw [ha k]
    _ = ∑ n ∈ F, a n * (sourceKernel M m n : ℂ) :=
          sum_signedFreq (fun n => a n * (sourceKernel M m n : ℂ))
    _ = crossRow M (6 / 5) F a m := by
          simp only [crossRow, sourceKernel, Complex.ofReal_mul, Complex.ofReal_add]
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun n _ => by ring

end AEGIS.CvSActualCrossRowL12V1

#print axioms AEGIS.CvSActualCrossRowL12V1.sourceKernel_diag
#print axioms AEGIS.CvSActualCrossRowL12V1.sourceKernel_off
#print axioms AEGIS.CvSActualCrossRowL12V1.sourceY_eq_actual_crossRow
