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

import AEGISOverlay.RHScaleRowCompositionV1

/-!
AEGIS Ω — exact four-block integer weighted Schur on the actual Weil B.
No new mathematical axioms, sorry, admit, RH premise, or surrogate Gram.
A source candidate until pinned Lean 4.33.1 compiles this exact revision.
-/

open Finset Complex
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHFourBlockIntegerWeightedSchurV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.RHGramExpansionV13

/-- Rational positive Schur weights 13-15-15-13. -/
def fourWeight (i : Fin 4) : ℝ :=
  if i.val = 0 ∨ i.val = 3 then 13 else 15

/-- Conservative exact mixed-entry costs for gaps 1, 2 and 3. -/
def fourCost (i j : Fin 4) : ℝ :=
  if i = j then 0 else
  if Nat.dist i.val j.val = 1 then (51 / 100 : ℝ) else
  if Nat.dist i.val j.val = 2 then (9 / 25 : ℝ) else
  (13 / 50 : ℝ)

theorem fourWeight_pos (i : Fin 4) : 0 < fourWeight i := by
  unfold fourWeight
  split_ifs <;> norm_num

theorem fourCost_nonneg (i j : Fin 4) : 0 ≤ fourCost i j := by
  unfold fourCost
  split_ifs <;> norm_num

theorem fourCost_diagonal (i : Fin 4) : fourCost i i = 0 := by
  simp [fourCost]

theorem fourCost_symmetric (i j : Fin 4) : fourCost i j = fourCost j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := Ne.symm hij
    simp only [fourCost, if_neg hij, if_neg hji, Nat.dist_comm]

/-- Weighted rows: 1643/1300 at the ends, 158/125 inside. -/
theorem fourCost_weighted_row (i : Fin 4) :
    (∑ j : Fin 4, fourCost i j * (fourWeight j / fourWeight i)) ≤
      (158 / 125 : ℝ) := by
  fin_cases i <;>
    simp +decide [fourCost, fourWeight, Fin.sum_univ_succ, Nat.dist] <;>
    norm_num

theorem fourBlock_margin_exact :
    (32 / 25 : ℝ) - (158 / 125 : ℝ) = 2 / 125 := by
  norm_num

/-- Exact, true-Weil four-block Schur coercivity.
The three genuine analytic B-entry estimates remain visible hypotheses. -/
theorem actual_four_block_weighted_coercive
    (gs : Fin 4 → WeilCompactSmoothGV1)
    (z : Fin 4 → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hdiag : ∀ i, (32 / 25 : ℝ) * E ≤ -(B (gs i) (gs i)).re)
    (hcross : ∀ i j, i ≠ j →
      ‖B (gs i) (gs j)‖ ≤ fourCost i j * E) :
    (B (packetSum z gs) (packetSum z gs)).re ≤
      -(2 / 125 : ℝ) * ∑ i : Fin 4, E * ‖z i‖ ^ 2 := by
  have hroot : Real.sqrt E * Real.sqrt E = E := by
    nlinarith [Real.sq_sqrt hE]
  have hcross' : ∀ i j : Fin 4, i ≠ j →
      ‖B (gs i) (gs j)‖ ≤
        fourCost i j * (Real.sqrt E * Real.sqrt E) := by
    intro i j hij
    rw [hroot]
    exact hcross i j hij
  have h := AEGIS.WeightedSchur.weighted_gram_variable_energy
    (fun i j => B (gs i) (gs j)) z (fun _ : Fin 4 => E)
    fourCost fourWeight (32 / 25 : ℝ) (158 / 125 : ℝ)
    (fun _ => hE) fourCost_nonneg fourCost_diagonal
    fourCost_symmetric fourWeight_pos hdiag hcross' fourCost_weighted_row
  rw [fourBlock_margin_exact] at h
  rw [B_packetSum]
  exact h

/-- Adapter retaining all three actual gap estimates and every Weil cross term. -/
theorem actual_four_block_coercive_of_three_gap_bounds
    (gs : Fin 4 → WeilCompactSmoothGV1)
    (z : Fin 4 → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hdiag : ∀ i, (32 / 25 : ℝ) * E ≤ -(B (gs i) (gs i)).re)
    (hgap1 : ∀ i j : Fin 4, Nat.dist i.val j.val = 1 →
      ‖B (gs i) (gs j)‖ ≤ (51 / 100 : ℝ) * E)
    (hgap2 : ∀ i j : Fin 4, Nat.dist i.val j.val = 2 →
      ‖B (gs i) (gs j)‖ ≤ (9 / 25 : ℝ) * E)
    (hgap3 : ∀ i j : Fin 4, Nat.dist i.val j.val = 3 →
      ‖B (gs i) (gs j)‖ ≤ (13 / 50 : ℝ) * E) :
    (B (packetSum z gs) (packetSum z gs)).re ≤
      -(2 / 125 : ℝ) * ∑ i : Fin 4, E * ‖z i‖ ^ 2 := by
  apply actual_four_block_weighted_coercive gs z E hE hdiag
  intro i j hij
  have hcases : Nat.dist i.val j.val = 1 ∨
      Nat.dist i.val j.val = 2 ∨
      Nat.dist i.val j.val = 3 := by
    fin_cases i <;> fin_cases j <;> norm_num [Nat.dist] at *
  rcases hcases with h1 | h2 | h3
  · simpa [fourCost, hij, h1] using hgap1 i j h1
  · simpa [fourCost, hij, h2] using hgap2 i j h2
  · simpa [fourCost, hij, h3] using hgap3 i j h3

/-- Separate outward Q16.16 rounding yields 1048 certified ticks. -/
theorem fourBlock_q16_margin :
    (1048 / 65536 : ℝ) < 2 / 125 ∧
      (83886 / 65536 : ℝ) ≤ 32 / 25 ∧
      (158 / 125 : ℝ) ≤ 82838 / 65536 ∧
      (83886 / 65536 : ℝ) - 82838 / 65536 = 1048 / 65536 := by
  norm_num

end AEGIS.RHFourBlockIntegerWeightedSchurV1

#print axioms AEGIS.RHFourBlockIntegerWeightedSchurV1.fourCost_weighted_row
#print axioms AEGIS.RHFourBlockIntegerWeightedSchurV1.actual_four_block_weighted_coercive
#print axioms AEGIS.RHFourBlockIntegerWeightedSchurV1.actual_four_block_coercive_of_three_gap_bounds
#print axioms AEGIS.RHFourBlockIntegerWeightedSchurV1.fourBlock_q16_margin
