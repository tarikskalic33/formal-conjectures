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


import AEGISOverlay.RHActualUniversalFineGramV1
import AEGISOverlay.RHWeightedSchurV1
import WeilAbjadFourPhaseBridgeV1

/-!
AEGIS Omega: source-only two-scale actual Weil row-budget bridge.
This imports the existing genuine-Weil signed-row consumer on PR #88.
The near/far inequalities are EXPLICIT hypotheses: no analytic bound
on the prime part or unconditional RH is claimed.
-/

open Finset
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHScaleRowCompositionV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHGramExpansionV13
open AEGIS.RHActualUniversalFineGramV1

/-- An arbitrary assignment of actual fine packets to macro blocks splits
    the entire off-diagonal row into same-block and cross-block terms.
    No entry is discarded, even if it is signed or negative. -/
theorem actual_row_eq_near_add_far
    {n : ℕ} (block : Fin (n + 1) → ℕ)
    (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) =
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i = block j then c i j else 0) +
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i ≠ block j then c i j else 0) := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : block i = block j
  · simp [h]
  · simp [h]

/-- A two-scale allocation implies the single actual row budget.
    There is no cardinality-dependent per-pair rounding. -/
theorem actual_row_le_of_near_far
    {n : ℕ} (block : Fin (n + 1) → ℕ)
    (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (near far : ℝ)
    (hnear : ∀ i : Fin (n + 1),
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i = block j then c i j else 0) ≤ near)
    (hfar : ∀ i : Fin (n + 1),
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i ≠ block j then c i j else 0) ≤ far) :
    ∀ i : Fin (n + 1),
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j) ≤ near + far := by
  intro i
  rw [actual_row_eq_near_add_far block c i]
  exact add_le_add (hnear i) (hfar i)

/-- The existing real-signed actual-Weil coercivity theorem is inherited
    from two *separately certified* scales. In particular, a verified
    near/far budget is not merely a toy Gram surrogate: the conclusion
    is the original arithmetic Weil B for the recomposed packet. -/
theorem actual_weil_coercive_of_two_scale_signed_rows
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (block : Fin (n + 1) → ℕ)
    (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (near far : ℝ)
    (hsym : ∀ i j, c i j = c j i)
    (hdiag : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (hcross : ∀ i j, i ≠ j →
      (B (gs i) (gs j)).re ≤
        c i j * (energy (gs i).1 + energy (gs j).1))
    (hnear : ∀ i : Fin (n + 1),
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i = block j then c i j else 0) ≤ near)
    (hfar : ∀ i : Fin (n + 1),
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i ≠ block j then c i j else 0) ≤ far)
    (hbudget : near + far ≤ (57430 / 65536 : ℝ)) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
      (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
        -(641 / 32768 : ℝ) * (∑ i, energy (gs i).1) := by
  apply actual_fine_gram_coercive_of_signed_real_row_certificate
    gs c hsym hdiag hcross
  intro i
  exact (actual_row_le_of_near_far block c near far hnear hfar i).trans hbudget

/-- Exact Q16.16 arithmetical allocation: splitting 57430 units over
    the two scales cannot exceed the budget. -/
theorem q16_two_scale_units
    (nearUnits farUnits : ℕ)
    (h : nearUnits + farUnits ≤ 57430) :
    (nearUnits : ℝ) / 65536 + (farUnits : ℝ) / 65536 ≤
      (57430 / 65536 : ℝ) := by
  have hh : ((nearUnits + farUnits : ℕ) : ℝ) ≤ (57430 : ℝ) := by
    exact_mod_cast h
  norm_num at hh ⊢
  linarith


/-! ## Coarse scale: exact local 9/64 control pays for every near interaction

Each macro packet may itself be the sum of arbitrarily many moment-zero
fine atoms. Its genuine diagonal is controlled by the existing local
nine-over-64 analytic theorem, not by an entrywise near-pair bound.
Only the cross-MACRO signed row remains a hypothesis. -/

/-- Coarse Weil packets each occupy their own 9/64 logarithmic window.
The actual local signed Gram is paid exactly. A signed cross-macro row
budget 2 * R + gap <= 1/10 then yields a quantitative global sign.
No cross-macro analytic estimate or universal producer is assumed. -/
theorem actual_nine_macro_coercive_of_signed_cross_rows
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : Fin (n + 1) → ℝ)
    (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (R gap : ℝ)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hwin : ∀ i, AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (gs i) (9 / 64) (center i))
    (hsym : ∀ i j, c i j = c j i)
    (hcross : ∀ i j, i ≠ j →
      (B (gs i) (gs j)).re ≤
        c i j * (energy (gs i).1 + energy (gs j).1))
    (hrow : ∀ i, (∑ j ∈
      (Finset.univ : Finset (Fin (n + 1))).erase i,
      c i j) ≤ R)
    (hbudget : 2 * R + gap ≤ (1 / 10 : ℝ)) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
       (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
      -gap * (∑ i, energy (gs i).1) := by
  have hd (i : Fin (n + 1)) :
      (1 / 10 : ℝ) * energy (gs i).1 ≤
        -(B (gs i) (gs i)).re := by
    have h := AEGIS.RHWindowNineOver64GlobalizationV14.nine_over_64_coercive
      (gs i) (center i) (hwin i) (hm i)
    change (B (gs i) (gs i)).re ≤
      -(1 / 10 : ℝ) * energy (gs i).1 at h
    linarith
  have hs :
      (∑ i, (1 / 10 : ℝ) * energy (gs i).1) ≤
      ∑ i, -(B (gs i) (gs i)).re :=
    Finset.sum_le_sum (fun i _ => hd i)
  have hdiag :
      (1 / 10 : ℝ) * (∑ i, energy (gs i).1) ≤
        -(∑ i, (B (gs i) (gs i)).re) := by
    rw [Finset.mul_sum]
    simpa only [Finset.sum_neg_distrib] using hs
  have hmixed := actual_mixed_defect_le_of_signed_symmetric_row
    gs c R hsym hcross hrow
  have hgram :
      (B (packetSum (fun _ => (1 : ℂ)) gs)
         (packetSum (fun _ => (1 : ℂ)) gs)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
    rw [B_packetSum]
    simp
  unfold AEGIS.RHActualMixedDefectV1.actualMixedDefect at hmixed
  rw [← hgram] at hmixed
  have hE : 0 ≤ (∑ i, energy (gs i).1) :=
    Finset.sum_nonneg (fun i _ => energy_nonnegative (gs i).1)
  have hbudgetE :
      (2 * R + gap) * (∑ i, energy (gs i).1) ≤
      (1 / 10 : ℝ) * (∑ i, energy (gs i).1) :=
    mul_le_mul_of_nonneg_right hbudget hE
  nlinarith

/-- Non-strict full global sign under the concrete macro row threshold 1/20. -/
theorem actual_nine_macro_nonpositive_of_signed_cross_rows
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : Fin (n + 1) → ℝ)
    (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hwin : ∀ i, AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (gs i) (9 / 64) (center i))
    (hsym : ∀ i j, c i j = c j i)
    (hcross : ∀ i j, i ≠ j →
      (B (gs i) (gs j)).re ≤
        c i j * (energy (gs i).1 + energy (gs j).1))
    (hrow : ∀ i, (∑ j ∈
      (Finset.univ : Finset (Fin (n + 1))).erase i,
      c i j) ≤ (1 / 20 : ℝ)) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
       (packetSum (fun _ => (1 : ℂ)) gs)).re ≤ 0 := by
  have h := actual_nine_macro_coercive_of_signed_cross_rows
    gs center c (1 / 20 : ℝ) 0 hm hwin hsym hcross hrow (by norm_num)
  simpa using h




/-! ## Exact signed near/interblock separation of the genuine Weil form

This identity refines the earlier generic row decomposition by operating on
the actual complex-Weil B entries. It retains all ordered off-diagonal
entries with their original signs. In particular, the interblock component
cannot be omitted after recomposition.
-/

/-- Actual signed interactions between atoms assigned to the same macro block. -/
def actualIntraBlockSignedDefect
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (block : Fin (n + 1) → ℕ) : ℝ :=
  ∑ i : Fin (n + 1),
    ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
      if block i = block j then (B (gs i) (gs j)).re else 0

/-- Actual signed interactions between different macro blocks. -/
def actualInterBlockSignedDefect
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (block : Fin (n + 1) → ℕ) : ℝ :=
  ∑ i : Fin (n + 1),
    ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
      if block i ≠ block j then (B (gs i) (gs j)).re else 0

/-- Exact decomposition, not a Schur estimate. For any grouping of any
finite genuine Weil atoms, the original signed mixed defect equals
the internal signed interactions plus all cross-block signed interactions. -/
theorem actual_mixed_defect_eq_block_signed_split
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (block : Fin (n + 1) → ℕ) :
    AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs =
      actualIntraBlockSignedDefect gs block +
        actualInterBlockSignedDefect gs block := by
  have hsplit (i : Fin (n + 1)) :
      (∑ j, (B (gs i) (gs j)).re) =
        (B (gs i) (gs i)).re +
          ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
            (B (gs i) (gs j)).re := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hdef :
      AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs =
        ∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          (B (gs i) (gs j)).re := by
    unfold AEGIS.RHActualMixedDefectV1.actualMixedDefect
    rw [Complex.re_sum]
    simp_rw [Complex.re_sum]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    ring
  calc
    AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs =
        ∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          (B (gs i) (gs j)).re := hdef
    _ = ∑ i, ((∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i = block j then (B (gs i) (gs j)).re else 0) +
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i ≠ block j then (B (gs i) (gs j)).re else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact actual_row_eq_near_add_far block
        (fun i j => (B (gs i) (gs j)).re) i
    _ = actualIntraBlockSignedDefect gs block +
        actualInterBlockSignedDefect gs block := by
      unfold actualIntraBlockSignedDefect actualInterBlockSignedDefect
      rw [Finset.sum_add_distrib]

/-- A source-true global criterion after any regrouping. Local internal
control and cross-macro control MUST be paid jointly; regrouping alone
cannot change the sign of B on the reconstructed packet. -/
theorem actual_sign_of_block_signed_split
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (block : Fin (n + 1) → ℕ)
    (hinternal : actualIntraBlockSignedDefect gs block ≤
      -(∑ i, (B (gs i) (gs i)).re) -
        actualInterBlockSignedDefect gs block) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
      (packetSum (fun _ => (1 : ℂ)) gs)).re ≤ 0 := by
  have hbudget :
      AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
        -(∑ i, (B (gs i) (gs i)).re) := by
    rw [actual_mixed_defect_eq_block_signed_split gs block]
    linarith
  have hgram :
      (B (packetSum (fun _ => (1 : ℂ)) gs)
         (packetSum (fun _ => (1 : ℂ)) gs)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
    rw [B_packetSum]
    simp
  unfold AEGIS.RHActualMixedDefectV1.actualMixedDefect at hbudget
  rw [hgram]
  linarith

/-! ## Exact signed recomposition: replace row-wise loss by a single total budget

On the already-formed macro packets, local 9/64 control pays every
intra-macro interaction. The only global certificate is the ACTUAL total
signed inter-macro defect, not a symmetric Schur row or an absolute norm.
This is strictly more flexible than per-row control but does not assert
that arbitrary packets admit a certified macro decomposition.
-/

/-- Global true-Weil coercivity on a finite family of local 9/64 macro
packets from ONE summed signed cross-macro bound. No pairwise row
majorant, positivity of mixed coefficients, or equal-energy constraint.
The full actual signed defect is the only external analytic input. -/
theorem actual_nine_macro_coercive_of_total_signed_defect
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : Fin (n + 1) → ℝ) (gap : ℝ)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hwin : ∀ i, AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (gs i) (9 / 64) (center i))
    (htotal :
      AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
        ((1 / 10 : ℝ) - gap) * (∑ i, energy (gs i).1)) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
      (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
      -gap * (∑ i, energy (gs i).1) := by
  have hd (i : Fin (n + 1)) :
      (1 / 10 : ℝ) * energy (gs i).1 ≤
        -(B (gs i) (gs i)).re := by
    have h := AEGIS.RHWindowNineOver64GlobalizationV14.nine_over_64_coercive
      (gs i) (center i) (hwin i) (hm i)
    change (B (gs i) (gs i)).re ≤
      -(1 / 10 : ℝ) * energy (gs i).1 at h
    linarith
  have hs :
      (∑ i, (1 / 10 : ℝ) * energy (gs i).1) ≤
      ∑ i, -(B (gs i) (gs i)).re :=
    Finset.sum_le_sum (fun i _ => hd i)
  have hdiag :
      (1 / 10 : ℝ) * (∑ i, energy (gs i).1) ≤
        -(∑ i, (B (gs i) (gs i)).re) := by
    rw [Finset.mul_sum]
    simpa only [Finset.sum_neg_distrib] using hs
  have hgram :
      (B (packetSum (fun _ => (1 : ℂ)) gs)
         (packetSum (fun _ => (1 : ℂ)) gs)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
    rw [B_packetSum]
    simp
  unfold AEGIS.RHActualMixedDefectV1.actualMixedDefect at htotal
  rw [← hgram] at htotal
  nlinarith

/-- The signed-total version can prove a nonpositive complete Gram even
when no per-row Schur certificate satisfies the 1/20 threshold. -/
theorem actual_nine_macro_nonpositive_of_total_signed_defect
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : Fin (n + 1) → ℝ)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hwin : ∀ i, AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (gs i) (9 / 64) (center i))
    (htotal :
      AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
        (1 / 10 : ℝ) * (∑ i, energy (gs i).1)) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
      (packetSum (fun _ => (1 : ℂ)) gs)).re ≤ 0 := by
  have h := actual_nine_macro_coercive_of_total_signed_defect
    gs center 0 hm hwin (by simpa using htotal)
  simpa using h

/-! ## Lossless Q16.16 accumulation, exactly as integer time-tick arithmetic

Integer-valued actual pair-cost certificates are accumulated as Nat
first. The near/far partition is an exact disjoint split of EVERY
off-diagonal entry. Only the final total is divided by 65536.
This is a proof about actual Weil Gram certificates, not a physical
temporal-resolution claim or an assumed universal prime bound. -/

/-- The integer pair costs of every actual off-diagonal entry are
partitioned without rounding, deletion, or double counting. -/
theorem q16_nat_row_eq_near_add_far
    {n : ℕ} (block : Fin (n + 1) → ℕ)
    (cost : Fin (n + 1) → Fin (n + 1) → ℕ)
    (i : Fin (n + 1)) :
    (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
      cost i j) =
    (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
      if block i = block j then cost i j else 0) +
    (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
      if block i ≠ block j then cost i j else 0) := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : block i = block j
  · simp [h]
  · simp [h]

/-- Exact finite, dimension-independent Q16.16 row-budget admission
from separate integer near and far ledgers. All pairwise estimates
remain about genuine complex Weil B, not a proxy matrix.

The analytic bound on each B entry is explicitly required; the
integer-row theorem itself only eliminates intermediate rounding. -/
theorem actual_fine_gram_q16_coercive_of_two_scale_integer_row
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (block : Fin (n + 1) → ℕ)
    (cost : Fin (n + 1) → Fin (n + 1) → ℕ)
    (nearUnits farUnits : ℕ)
    (hsym : ∀ i j, cost i j = cost j i)
    (hdiag : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (hcross : ∀ i j, i ≠ j →
      ‖B (gs i) (gs j)‖ ≤
        actualQ16PairCost cost i j *
          (energy (gs i).1 + energy (gs j).1))
    (hnear : ∀ i : Fin (n + 1),
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i = block j then cost i j else 0) ≤ nearUnits)
    (hfar : ∀ i : Fin (n + 1),
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i ≠ block j then cost i j else 0) ≤ farUnits)
    (hbudget : nearUnits + farUnits ≤ 57430) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
       (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
      -(641 / 32768 : ℝ) * (∑ i, energy (gs i).1) := by
  apply actual_fine_gram_q16_coercive_of_pair_certificate
    gs cost hsym hdiag hcross
  intro i
  calc
    (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
      cost i j) =
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i = block j then cost i j else 0) +
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i ≠ block j then cost i j else 0) :=
          q16_nat_row_eq_near_add_far block cost i
    _ ≤ nearUnits + farUnits := add_le_add (hnear i) (hfar i)
    _ ≤ 57430 := hbudget


/-- Signed-real Q16.16 near/far consumer with *integer-only* ledger
accumulation. Unlike the norm version, only upper bounds on the
actual signed real Weil mixed entries are needed. Exact row sums are
checked as Naturals before the single 65536 denominator is applied.

No sign is assigned to any prime term and no unconditional analytic
prime estimate is assumed by this theorem. -/
theorem actual_fine_gram_q16_signed_of_two_scale_integer_row
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (block : Fin (n + 1) → ℕ)
    (cost : Fin (n + 1) → Fin (n + 1) → ℕ)
    (nearUnits farUnits : ℕ)
    (hsym : ∀ i j, cost i j = cost j i)
    (hdiag : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (hcross : ∀ i j, i ≠ j →
      (B (gs i) (gs j)).re ≤
        actualQ16PairCost cost i j *
          (energy (gs i).1 + energy (gs j).1))
    (hnear : ∀ i : Fin (n + 1),
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i = block j then cost i j else 0) ≤ nearUnits)
    (hfar : ∀ i : Fin (n + 1),
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i ≠ block j then cost i j else 0) ≤ farUnits)
    (hbudget : nearUnits + farUnits ≤ 57430) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
       (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
      -(641 / 32768 : ℝ) * (∑ i, energy (gs i).1) := by
  have hc : ∀ i j,
      actualQ16PairCost cost i j = actualQ16PairCost cost j i := by
    intro i j
    dsimp [actualQ16PairCost]
    rw [hsym i j]
  apply actual_fine_gram_coercive_of_signed_real_row_certificate
    gs (actualQ16PairCost cost) hc hdiag hcross
  intro i
  have hrowNat :
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        cost i j) ≤ 57430 := by
    calc
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        cost i j) =
        (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          if block i = block j then cost i j else 0) +
        (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          if block i ≠ block j then cost i j else 0) :=
            q16_nat_row_eq_near_add_far block cost i
      _ ≤ nearUnits + farUnits := add_le_add (hnear i) (hfar i)
      _ ≤ 57430 := hbudget
  change (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
    (cost i j : ℝ) / 65536) ≤ (57430 / 65536 : ℝ)
  calc
    (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
      (cost i j : ℝ) / 65536) =
      (((∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        cost i j : ℕ) : ℝ) / 65536) := by
          simp only [Finset.sum_div, Nat.cast_sum]
    _ ≤ (57430 / 65536 : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hrowNat) (by norm_num)


/-! ## Directed weighted Schur rows, with exact Q16.16 integer admission

A weighted Schur row is not obtained by merely multiplying an
unweighted sum-energy majorant by an arbitrary weight. Instead the
ACTUAL signed Weil coefficient has the explicit *directed* bound

  Re B(i,j) ≤ c(i,j) E(i) + c(j,i) E(j).

No symmetry or positivity of the directed c matrix is necessary.
This permits unequal energies and distinct weights. The row estimate
is exact, and no negative real mixed coefficient is discarded.

For positive integer weights w and natural Q16.16 cost tickets k,
c(i,j) = k(i,j)*w(j)/(65536*w(i)). Requiring a natural-number
weighted row bound closes the finite arithmetic Schur step.

It does NOT construct k or prove the analytic cross-packet bound:
those remain explicit hypotheses for the universal producer. -/

/-- Actual mixed Weil defect obeys a *directed* Schur upper row budget.
No symmetric-cost assumption is needed, because the second directed
term is transposed over the entire off-diagonal index set. -/
theorem actual_mixed_defect_le_of_directed_rows
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (c : Fin (n + 1) → Fin (n + 1) → ℝ) (R : ℝ)
    (hcross : ∀ i j, i ≠ j →
      (B (gs i) (gs j)).re ≤
        c i j * energy (gs i).1 + c j i * energy (gs j).1)
    (hrow : ∀ i, (∑ j ∈
      (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) ≤ R) :
    AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
      (2 * R) * (∑ i, energy (gs i).1) := by
  let E : Fin (n + 1) → ℝ := fun i => energy (gs i).1
  have hsplit (i : Fin (n + 1)) :
      (∑ j, (B (gs i) (gs j)).re) =
        (B (gs i) (gs i)).re +
          ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
            (B (gs i) (gs j)).re := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hdef :
      AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs =
        ∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          (B (gs i) (gs j)).re := by
    unfold AEGIS.RHActualMixedDefectV1.actualMixedDefect
    rw [Complex.re_sum]
    simp_rw [Complex.re_sum]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    ring
  have hoff :
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        (B (gs i) (gs j)).re) ≤
      ∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        (c i j * E i + c j i * E j) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j hj
    have hij : i ≠ j := by
      intro h
      exact (Finset.mem_erase.mp hj).1 h.symm
    exact hcross i j hij
  have htranspose :
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c j i * E j) =
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j * E i) := by
    simpa using (AEGIS.RHGramExpansionV13.sum_erase_comm
      (fun i j : Fin (n + 1) => c j i * E j))
  have hfactor :
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j * E i) =
      ∑ i, E i * (∑ j ∈
        (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hdouble :
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        (c i j * E i + c j i * E j)) =
      2 * (∑ i, E i * (∑ j ∈
        (Finset.univ : Finset (Fin (n + 1))).erase i, c i j)) := by
    calc
      _ = (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
             c i j * E i) +
          (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
             c j i * E j) := by
           simp only [Finset.sum_add_distrib]
      _ = 2 * (∑ i, E i * (∑ j ∈
          (Finset.univ : Finset (Fin (n + 1))).erase i, c i j)) := by
           rw [htranspose]
           simp only [hfactor]
           ring
  have htotal :
      (∑ i, E i * (∑ j ∈
        (Finset.univ : Finset (Fin (n + 1))).erase i, c i j)) ≤
      R * (∑ i, E i) := by
    calc
      _ ≤ ∑ i, E i * R := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hrow i)
          (energy_nonnegative (gs i).1)
      _ = R * (∑ i, E i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  calc
    AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs =
        (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          (B (gs i) (gs j)).re) := hdef
    _ ≤ (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          (c i j * E i + c j i * E j)) := hoff
    _ = 2 * (∑ i, E i * (∑ j ∈
          (Finset.univ : Finset (Fin (n + 1))).erase i, c i j)) := hdouble
    _ ≤ 2 * (R * (∑ i, E i)) :=
      mul_le_mul_of_nonneg_left htotal (by norm_num)
    _ = (2 * R) * (∑ i, energy (gs i).1) := by
      dsimp [E]
      ring

/-- The original arithmetic Weil Gram is coercive from directed weighted
integer row certificates. All Q16.16 divisions happen AFTER multiplying
and summing exact integer costs and integer weights.

The pairwise *analytic* directed inequality is an explicit premise, not
derived from numerical rounding or the preceding eleven-block sources. -/
theorem actual_weighted_q16_coercive_of_integer_rows
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (cost : Fin (n + 1) → Fin (n + 1) → ℕ)
    (weight : Fin (n + 1) → ℕ)
    (hw : ∀ i, 0 < weight i)
    (hdiag : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (hcross : ∀ i j, i ≠ j →
      (B (gs i) (gs j)).re ≤
        ((cost i j : ℝ) * (weight j : ℝ) /
          ((weight i : ℝ) * 65536)) * energy (gs i).1 +
        ((cost j i : ℝ) * (weight i : ℝ) /
          ((weight j : ℝ) * 65536)) * energy (gs j).1)
    (hrow : ∀ i : Fin (n + 1),
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        cost i j * weight j) ≤ 57430 * weight i) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
       (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
      -(641 / 32768 : ℝ) * (∑ i, energy (gs i).1) := by
  let c : Fin (n + 1) → Fin (n + 1) → ℝ := fun i j =>
    (cost i j : ℝ) * (weight j : ℝ) / ((weight i : ℝ) * 65536)
  have hc (i : Fin (n + 1)) :
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j) ≤ (57430 / 65536 : ℝ) := by
    have hwi : (0 : ℝ) < (weight i : ℝ) := by
      exact_mod_cast hw i
    have hden : (0 : ℝ) < (weight i : ℝ) * 65536 :=
      mul_pos hwi (by norm_num)
    have hrowReal :
        (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          (cost i j : ℝ) * (weight j : ℝ)) ≤
          (57430 : ℝ) * (weight i : ℝ) := by
      exact_mod_cast hrow i
    change (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
      (cost i j : ℝ) * (weight j : ℝ) /
        ((weight i : ℝ) * 65536)) ≤ (57430 / 65536 : ℝ)
    rw [← Finset.sum_div]
    apply (div_le_iff₀ hden).mpr
    calc
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        (cost i j : ℝ) * (weight j : ℝ)) ≤
          (57430 : ℝ) * (weight i : ℝ) := hrowReal
      _ = (57430 / 65536 : ℝ) * ((weight i : ℝ) * 65536) := by ring
  have hdefect := actual_mixed_defect_le_of_directed_rows
    gs c (57430 / 65536 : ℝ) hcross hc
  have hlocal := fine_mixed_defect_lower_bound n gs hdiag
  have hgram :
      (B (packetSum (fun _ => (1 : ℂ)) gs)
        (packetSum (fun _ => (1 : ℂ)) gs)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
    rw [B_packetSum]
    simp
  rw [← hgram] at hlocal
  have hE : 0 ≤ (∑ i, energy (gs i).1) :=
    Finset.sum_nonneg (fun i _ => energy_nonnegative (gs i).1)
  have hround :
      (116142 / 65536 : ℝ) * (∑ i, energy (gs i).1) ≤
        (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1) :=
    mul_le_mul_of_nonneg_right (by norm_num) hE
  linarith

/-- Optional multiscale ledger. Near/far weighted costs are added in
Nat, and only the final exact weighted Schur budget is converted to
a real upper bound. No cost is silently rounded away. -/
theorem actual_weighted_q16_coercive_of_two_scale_rows
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (block : Fin (n + 1) → ℕ)
    (cost : Fin (n + 1) → Fin (n + 1) → ℕ)
    (weight : Fin (n + 1) → ℕ)
    (nearUnits farUnits : ℕ)
    (hw : ∀ i, 0 < weight i)
    (hdiag : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (hcross : ∀ i j, i ≠ j →
      (B (gs i) (gs j)).re ≤
        ((cost i j : ℝ) * (weight j : ℝ) /
          ((weight i : ℝ) * 65536)) * energy (gs i).1 +
        ((cost j i : ℝ) * (weight i : ℝ) /
          ((weight j : ℝ) * 65536)) * energy (gs j).1)
    (hnear : ∀ i : Fin (n + 1),
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i = block j then cost i j * weight j else 0) ≤
          nearUnits * weight i)
    (hfar : ∀ i : Fin (n + 1),
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i ≠ block j then cost i j * weight j else 0) ≤
          farUnits * weight i)
    (hbudget : nearUnits + farUnits ≤ 57430) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
       (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
      -(641 / 32768 : ℝ) * (∑ i, energy (gs i).1) := by
  apply actual_weighted_q16_coercive_of_integer_rows gs cost weight
    hw hdiag hcross
  intro i
  calc
    (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
      cost i j * weight j) =
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i = block j then cost i j * weight j else 0) +
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i ≠ block j then cost i j * weight j else 0) :=
          q16_nat_row_eq_near_add_far block (fun i j => cost i j * weight j) i
    _ ≤ nearUnits * weight i + farUnits * weight i :=
          add_le_add (hnear i) (hfar i)
    _ = (nearUnits + farUnits) * weight i := by ring
    _ ≤ 57430 * weight i := Nat.mul_le_mul_right (weight i) hbudget


/-! ## Abjad's exact four-phase tests as a Weil/Schur interface

The EXISTING source-pinned AEGIS module WeilAbjadFourPhaseBridgeV1
proves that the four triadic nodes 0,3,6,9 encode 1,I,-1,-I.
Here the actual Weil cross coefficient B(p,q), not a stand-in
complex variable, is passed to that exact four-phase theorem.

Nonnegativity of all four phase tests is still a specific ANALYTIC
obligation. We neither infer it from modular Abjad arithmetic nor
silently assume a global Weil sign. -/

/-- Actual Weil cross real-part bound from the full Abjad quarter-turn
phase tests. The bound is obtained by an existing formal equivalence
with the exact component-box condition on B, not a fresh assertion
of nonnegative zeta/Weil forms. -/
theorem actual_weil_re_le_of_abjad_four_phases
    (p q : WeilCompactSmoothGV1) (a : ℝ)
    (hphase : ∀ r : ℕ, AbjadTriadicNodeV1 r →
      0 ≤ WeilTwoPointValueV1 a (B p q) (AbjadPhaseV1 r)) :
    (B p q).re ≤ a := by
  have hcomponent :=
    (weil_abjad_triadic_nonnegative_iff_components_v1
      a (B p q)).mp hphase
  exact (le_abs_self (B p q).re).trans hcomponent.1

/-- Direct reconstruction of the true Weil cross coefficient using
opposite pairs of triadic Abjad phase nodes. All four identities come
from the original pinned WeilAbjadFourPhaseBridgeV1 source. -/
theorem actual_weil_abjad_four_phase_reconstruction
    (p q : WeilCompactSmoothGV1) (a : ℝ) :
    WeilTwoPointValueV1 a (B p q) (AbjadPhaseV1 0) +
        WeilTwoPointValueV1 a (B p q) (AbjadPhaseV1 6) = 4 * a ∧
    WeilTwoPointValueV1 a (B p q) (AbjadPhaseV1 3) +
        WeilTwoPointValueV1 a (B p q) (AbjadPhaseV1 9) = 4 * a ∧
    WeilTwoPointValueV1 a (B p q) (AbjadPhaseV1 0) -
        WeilTwoPointValueV1 a (B p q) (AbjadPhaseV1 6) =
          4 * (B p q).re ∧
    WeilTwoPointValueV1 a (B p q) (AbjadPhaseV1 9) -
        WeilTwoPointValueV1 a (B p q) (AbjadPhaseV1 3) =
          4 * (B p q).im := by
  exact weil_abjad_phase_reconstruction_v1 a (B p q)

/-- Abjad-to-weighted-Schur adapter with the actual Weil B and exact
directed Q16.16 integer ledgers. This theorem does NOT prove the
four phase positivity hypotheses; it only discharges their correct
algebraic transport to the true signed Gram. -/
theorem actual_weil_weighted_q16_of_abjad_phase_rows
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (block : Fin (n + 1) → ℕ)
    (cost : Fin (n + 1) → Fin (n + 1) → ℕ)
    (weight : Fin (n + 1) → ℕ)
    (nearUnits farUnits : ℕ)
    (hw : ∀ i, 0 < weight i)
    (hdiag : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (hphase : ∀ i j, i ≠ j → ∀ r : ℕ,
      AbjadTriadicNodeV1 r →
      0 ≤ WeilTwoPointValueV1
        (((cost i j : ℝ) * (weight j : ℝ) /
          ((weight i : ℝ) * 65536)) * energy (gs i).1 +
         ((cost j i : ℝ) * (weight i : ℝ) /
          ((weight j : ℝ) * 65536)) * energy (gs j).1)
        (B (gs i) (gs j)) (AbjadPhaseV1 r))
    (hnear : ∀ i : Fin (n + 1),
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i = block j then cost i j * weight j else 0) ≤
          nearUnits * weight i)
    (hfar : ∀ i : Fin (n + 1),
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i ≠ block j then cost i j * weight j else 0) ≤
          farUnits * weight i)
    (hbudget : nearUnits + farUnits ≤ 57430) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
       (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
      -(641 / 32768 : ℝ) * (∑ i, energy (gs i).1) := by
  apply actual_weighted_q16_coercive_of_two_scale_rows
    gs block cost weight nearUnits farUnits hw hdiag
    (by
      intro i j hij
      exact actual_weil_re_le_of_abjad_four_phases (gs i) (gs j)
        _ (hphase i j hij))
    hnear hfar hbudget


/-! ## Strongest existing weighted margin, without equal-energy atoms

The generic weighted Schur proof previously served eleven translates of
one mother packet and one common energy. An arbitrary finite fine Weil
partition consists of distinct shapes with unequal energies. This adapter
uses the already verified analytic fine diagonal gain for each atom and
the same exact 46708/65536 weighted row ceiling. The square-root
cross estimates are explicit obligations for the actual Weil B.
No mother-packet or translation assumption is imposed. -/

/-- The 34717/32768 margin holds for any finite genuine Weil packet
family, with different energies and arbitrary complex coefficients,
provided the *actual* mixed terms satisfy the stated weighted square-
root-energy Schur estimate. The universal analytic producer is not
smuggled into the theorem as an unverified fact. -/
theorem actual_weighted_schur_unequal_energy_from_fine_diagonals
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (z : Fin (n + 1) → ℂ)
    (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (w : Fin (n + 1) → ℝ)
    (hc : ∀ i j, 0 ≤ c i j)
    (hzero : ∀ i, c i i = 0)
    (hsym : ∀ i j, c i j = c j i)
    (hw : ∀ i, 0 < w i)
    (hdiag : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (hcross : ∀ i j, i ≠ j →
      ‖B (gs i) (gs j)‖ ≤ c i j *
        (Real.sqrt (energy (gs i).1) *
          Real.sqrt (energy (gs j).1)))
    (hrow : ∀ i, ∑ j, c i j * (w j / w i) ≤
      (46708 / 65536 : ℝ)) :
    (B (packetSum z gs) (packetSum z gs)).re ≤
      -(34717 / 32768 : ℝ) *
        (∑ i, energy (gs i).1 * ‖z i‖ ^ 2) := by
  have hdiagonal :
      ∀ i, (116142 / 65536 : ℝ) * energy (gs i).1 ≤
        -(B (gs i) (gs i)).re := by
    intro i
    exact (mul_le_mul_of_nonneg_right
      (by norm_num : (116142 / 65536 : ℝ) ≤ 5671 / 3200)
      (energy_nonnegative (gs i).1)).trans (hdiag i)
  have h := AEGIS.WeightedSchur.weighted_gram_variable_energy
    (fun i j => B (gs i) (gs j)) z
    (fun i => energy (gs i).1) c w
    (116142 / 65536 : ℝ) (46708 / 65536 : ℝ)
    (fun i => energy_nonnegative (gs i).1)
    hc hzero hsym hw hdiagonal hcross hrow
  have hmargin :
      (116142 / 65536 : ℝ) - 46708 / 65536 = 34717 / 32768 :=
    by norm_num
  rw [hmargin] at h
  rw [B_packetSum]
  exact h


/-- The exact optimized 46688/65536 cost budget applies to *any* finite
family of actual Weil atoms with potentially unequal energies, provided
the genuine mixed B entries obey the explicit square-root energy cost
and the indicated weighted row inequalities. Unlike the eleven-translate
producer, this adapter assumes neither a common seed nor a common energy.
It does NOT construct those rows for arbitrary moment-zero packets. -/
theorem actual_optimized_weighted_schur_unequal_energy_from_fine_diagonals
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (z : Fin (n + 1) → ℂ)
    (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (w : Fin (n + 1) → ℝ)
    (hc : ∀ i j, 0 ≤ c i j)
    (hzero : ∀ i, c i i = 0)
    (hsym : ∀ i j, c i j = c j i)
    (hw : ∀ i, 0 < w i)
    (hdiag : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (hcross : ∀ i j, i ≠ j →
      ‖B (gs i) (gs j)‖ ≤ c i j *
        (Real.sqrt (energy (gs i).1) *
          Real.sqrt (energy (gs j).1)))
    (hrow : ∀ i, ∑ j, c i j * (w j / w i) ≤
      (46688 / 65536 : ℝ)) :
    (B (packetSum z gs) (packetSum z gs)).re ≤
      -(34727 / 32768 : ℝ) *
        (∑ i, energy (gs i).1 * ‖z i‖ ^ 2) := by
  have hdiagonal :
      ∀ i, (116142 / 65536 : ℝ) * energy (gs i).1 ≤
        -(B (gs i) (gs i)).re := by
    intro i
    exact (mul_le_mul_of_nonneg_right
      (by norm_num : (116142 / 65536 : ℝ) ≤ 5671 / 3200)
      (energy_nonnegative (gs i).1)).trans (hdiag i)
  have h := AEGIS.WeightedSchur.weighted_gram_variable_energy
    (fun i j => B (gs i) (gs j)) z
    (fun i => energy (gs i).1) c w
    (116142 / 65536 : ℝ) (46688 / 65536 : ℝ)
    (fun i => energy_nonnegative (gs i).1)
    hc hzero hsym hw hdiagonal hcross hrow
  have hmargin :
      (116142 / 65536 : ℝ) - 46688 / 65536 =
        34727 / 32768 := by norm_num
  rw [hmargin] at h
  rw [B_packetSum]
  exact h

end AEGIS.RHScaleRowCompositionV1

#print axioms AEGIS.RHScaleRowCompositionV1.actual_row_eq_near_add_far
#print axioms AEGIS.RHScaleRowCompositionV1.actual_row_le_of_near_far
#print axioms AEGIS.RHScaleRowCompositionV1.actual_weil_coercive_of_two_scale_signed_rows
#print axioms AEGIS.RHScaleRowCompositionV1.q16_two_scale_units

#print axioms AEGIS.RHScaleRowCompositionV1.actual_nine_macro_coercive_of_signed_cross_rows
#print axioms AEGIS.RHScaleRowCompositionV1.actual_nine_macro_nonpositive_of_signed_cross_rows
#print axioms AEGIS.RHScaleRowCompositionV1.actual_nine_macro_coercive_of_total_signed_defect
#print axioms AEGIS.RHScaleRowCompositionV1.actual_nine_macro_nonpositive_of_total_signed_defect
#print axioms AEGIS.RHScaleRowCompositionV1.actual_mixed_defect_eq_block_signed_split
#print axioms AEGIS.RHScaleRowCompositionV1.actual_sign_of_block_signed_split
#print axioms AEGIS.RHScaleRowCompositionV1.q16_nat_row_eq_near_add_far
#print axioms AEGIS.RHScaleRowCompositionV1.actual_fine_gram_q16_coercive_of_two_scale_integer_row
#print axioms AEGIS.RHScaleRowCompositionV1.actual_fine_gram_q16_signed_of_two_scale_integer_row
#print axioms AEGIS.RHScaleRowCompositionV1.actual_mixed_defect_le_of_directed_rows
#print axioms AEGIS.RHScaleRowCompositionV1.actual_weighted_q16_coercive_of_integer_rows
#print axioms AEGIS.RHScaleRowCompositionV1.actual_weighted_q16_coercive_of_two_scale_rows
#print axioms AEGIS.RHScaleRowCompositionV1.actual_weil_re_le_of_abjad_four_phases
#print axioms AEGIS.RHScaleRowCompositionV1.actual_weil_abjad_four_phase_reconstruction
#print axioms AEGIS.RHScaleRowCompositionV1.actual_weil_weighted_q16_of_abjad_phase_rows
#print axioms AEGIS.RHScaleRowCompositionV1.actual_weighted_schur_unequal_energy_from_fine_diagonals

#print axioms AEGIS.RHScaleRowCompositionV1.actual_optimized_weighted_schur_unequal_energy_from_fine_diagonals
