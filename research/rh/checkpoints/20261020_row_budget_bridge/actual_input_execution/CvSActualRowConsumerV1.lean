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
/- Exact finite-row and Gram-tail contracts of the existing fixed-window consumer.
Original-import replay candidate until a source-bound receipt records PASS. -/
import CvSActualBasisBudgetV1
import CvSRealTailFormV1
import CvSProjectedBasisL12V1
open scoped BigOperators ComplexConjugate
namespace AEGIS.CvSActualRowConsumerV1
open AEGIS.CvSProjectedPackedCertificateL12V1 AEGIS.CvSProjectedTransportL12V1
open AEGIS.CvSSchurClosureFromBoundsV1 AEGIS.CvSProjectedSchurBridgeL12V1
open AEGIS.CvSLowBlockMatrixV1 AEGIS.CvSMomentBasisV1 AEGIS.CvSCrossCertV1
open AEGIS.CvSActualRowInputL12V1 AEGIS.CvSActualCrossRowL12V1
open AEGIS.CvSSourceProductAllV1 AEGIS.CvSGramTailV1
open AEGIS.CvSActualBasisBudgetV1 AEGIS.CvSRealTailFormV1
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

abbrev supports := fun i : Fin 139 => sinSqSupport (atomCenter i)
noncomputable abbrev weights := fun i : Fin 139 => sinSqWeight (atomCenter i)
noncomputable def a (v : Fin 139 → ℂ) := lowCoeff (6/5) supports weights (R_basis v)
noncomputable def lambdaApply (v : Fin 139 → ℂ) (j : Fin 139) : ℂ :=
  ∑ i, (lambdaReal j i : ℂ) * v i

/-- The original atom-row convention is the original coefficient map. -/
theorem sum_atomRow {p : ℕ} (L : ℝ) (S : Fin p → Finset ℤ)
    (b : Fin p → ℤ → ℂ) (c : Fin p → ℂ) (m : ℤ) :
    (∑ i, c i * atomRow L S b i m) = lowCoeff L S b c m := by
  simp only [atomRow, lowCoeff, Pi.single_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The certified residual acts on exactly the actual cross row and projected atom row. -/
theorem sourceZ_apply (M : ℕ) (v : Fin 139 → ℂ) (r : Fin 301) :
    (∑ i, (sourceZ M lambdaReal r i : ℂ) * v i) =
      crossRow M (6/5) (lowFreq supports) (a v) (rowIndex r) -
        ∑ j, R_basis (lambdaApply v) j * atomRow (6/5) supports weights j (rowIndex r) := by
  rw [sum_atomRow]
  by_cases hr : 80 ≤ r.val ∧ r.val < 221
  · have he : signedFreq (⟨r.val - 80, by omega⟩ : Fin 141) = rowIndex r := by
      change ((r.val - 80 : ℕ) : ℤ) - 70 = (r.val : ℤ) - 150
      omega
    have hcoeff := transformed_coeff_eq_lowCoeff (lambdaApply v)
      (⟨r.val - 80, by omega⟩ : Fin 141)
    rw [he] at hcoeff
    simp only [sourceZ, dif_pos hr]
    rw [residual_apply]
    rw [sourceY_eq_actual_crossRow]
    exact congrArg (fun z => crossRow M (6/5) (lowFreq supports) (a v) (rowIndex r) - z) hcoeff
  · have hn : rowIndex r ∉ lowFreq supports := by
      rw [lowFreq_mem_iff]
      unfold rowIndex
      omega
    rw [lowCoeff_eq_zero (6/5) supports weights _ hn, sub_zero]
    simp only [sourceZ, dif_neg hr]
    exact sourceY_eq_actual_crossRow M (rowIndex r) v

/-- All 301 certified residuals are precisely the rows -150 through 150. -/
theorem residual_energy_eq (M : ℕ) (v : Fin 139 → ℂ) :
    (∑ r : Fin 301, ‖∑ i, (sourceZ M lambdaReal r i : ℂ) * v i‖^2) =
      ∑ m ∈ Finset.Icc (-150 : ℤ) 150,
        ‖crossRow M (6/5) (lowFreq supports) (a v) m -
          ∑ j, R_basis (lambdaApply v) j * atomRow (6/5) supports weights j m‖^2 := by
  simp_rw [sourceZ_apply]
  exact sum_centered_rows (V := ℝ) 150 (fun m =>
    ‖crossRow M (6/5) (lowFreq supports) (a v) m -
      ∑ j, R_basis (lambdaApply v) j * atomRow (6/5) supports weights j m‖^2)

/-- Existing signed-frequency bijection, applied in both slots of a Hermitian form. -/
theorem signed_gform (v : ℤ → ℂ) (g : ℤ → ℤ → ℝ) :
    (∑ k : Fin 141, ∑ l : Fin 141,
      v (signedFreq k) * conj (v (signedFreq l)) * (g (signedFreq k) (signedFreq l) : ℂ)).re =
      gform (lowFreq supports) v g := by
  have h : (∑ k : Fin 141, ∑ l : Fin 141,
      v (signedFreq k) * conj (v (signedFreq l)) * (g (signedFreq k) (signedFreq l) : ℂ)) =
      ∑ k ∈ lowFreq supports, ∑ l ∈ lowFreq supports, v k * conj (v l) * (g k l : ℂ) := by
    calc
      _ = ∑ k : Fin 141, ∑ l ∈ lowFreq supports,
          v (signedFreq k) * conj (v l) * (g (signedFreq k) l : ℂ) :=
        Finset.sum_congr rfl (fun k _ => sum_signedFreq
          (fun l => v (signedFreq k) * conj (v l) * (g (signedFreq k) l : ℂ)))
      _ = _ := sum_signedFreq (fun k => ∑ l ∈ lowFreq supports, v k * conj (v l) * (g k l : ℂ))
  exact congrArg Complex.re h

/-- The real tail table is exactly the existing epsilon=1, T=13 Gram-tail expression. -/
theorem actual_tail_eq (M : ℕ) (v : Fin 139 → ℂ) :
    (∑ i, ∑ j, v i * conj (v j) *
      (AEGIS.CvSRealTailMatrixV1.tailMatrix transformedCoeff
        (fun k l => gramUp 150 (signedFreq k) (signedFreq l))
        (fun k => AEGIS.CvSRowTailV1.tau M (6/5) (signedFreq k))
        (((6/5 : ℝ)/Real.pi)^2) i j : ℂ)).re =
      gramTail M (6/5) (lowFreq supports) (a v) 13 1 150 := by
  rw [tail_form_eq]
  simp_rw [transformed_coeff_eq_lowCoeff]
  have h1 := signed_gform (fun n => a v n * (AEGIS.CvSRowTailV1.tau M (6/5) n : ℂ)) (gramUp 150)
  have h2 := signed_gform (a v) (gramUp 150)
  simp only [a] at h1 h2
  rw [h1, h2]
  norm_num [gramTail, a]

/-- Exact hfin identity; no positivity or numerical bound is assumed. -/
theorem budget_eq_rows (M : ℕ) (v : Fin 139 → ℂ) :
    actualBudget M v =
      (∑ m ∈ Finset.Icc (-150 : ℤ) 150,
        ‖crossRow M (6/5) (lowFreq supports) (a v) m -
          ∑ j, R_basis (lambdaApply v) j * atomRow (6/5) supports weights j m‖^2) +
        gramTail M (6/5) (lowFreq supports) (a v) 13 1 150 := by
  unfold actualBudget AEGIS.CvSRowBudgetGramBridgeV1.budgetEnergy
  rw [residual_energy_eq, actual_tail_eq]

noncomputable def coordinates (c : Fin 139 → ℂ) : Fin 139 → ℂ :=
  Classical.choose (AEGIS.CvSProjectedBasisL12V1.R_basis_surjective c)

theorem coordinates_spec (c : Fin 139 → ℂ) : R_basis (coordinates c) = c :=
  Classical.choose_spec (AEGIS.CvSProjectedBasisL12V1.R_basis_surjective c)

noncomputable def lam (c : Fin 139 → ℂ) : Fin 139 → ℂ := R_basis (lambdaApply (coordinates c))
noncomputable def Brow (M : ℕ) (c : Fin 139 → ℂ) : ℝ := actualBudget M (coordinates c)

/-- The existing fixed-window consumer's finite-row premise, now for every original coefficient vector. -/
theorem hfin (M : ℕ) (c : Fin 139 → ℂ) :
    (∑ m ∈ Finset.Icc (-150 : ℤ) 150,
      ‖crossRow M (6/5) (lowFreq supports) (lowCoeff (6/5) supports weights c) m -
        ∑ j, lam c j * atomRow (6/5) supports weights j m‖^2) +
      gramTail M (6/5) (lowFreq supports) (lowCoeff (6/5) supports weights c) 13 1 150 ≤ Brow M c := by
  have h := budget_eq_rows M (coordinates c)
  simpa only [Brow, lam, a, coordinates_spec] using h.symm.le

/-- The existing fixed-window consumer's relative Schur budget, with kappa=40. -/
theorem hB (M : ℕ) (hM : 3 ≤ M) (c : Fin 139 → ℂ) :
    Brow M c ≤ 40 * Q_CvS M (6/5) atomCenter c := by
  have h := actualBudget_le_original M hM (coordinates c)
  simpa only [Brow, coordinates_spec] using h
end AEGIS.CvSActualRowConsumerV1
#print axioms AEGIS.CvSActualRowConsumerV1.sum_atomRow
#print axioms AEGIS.CvSActualRowConsumerV1.sourceZ_apply
#print axioms AEGIS.CvSActualRowConsumerV1.residual_energy_eq
#print axioms AEGIS.CvSActualRowConsumerV1.signed_gform
#print axioms AEGIS.CvSActualRowConsumerV1.actual_tail_eq
#print axioms AEGIS.CvSActualRowConsumerV1.budget_eq_rows
#print axioms AEGIS.CvSActualRowConsumerV1.coordinates_spec
#check @AEGIS.CvSActualRowConsumerV1.hfin
#print axioms AEGIS.CvSActualRowConsumerV1.hfin
#check @AEGIS.CvSActualRowConsumerV1.hB
#print axioms AEGIS.CvSActualRowConsumerV1.hB
