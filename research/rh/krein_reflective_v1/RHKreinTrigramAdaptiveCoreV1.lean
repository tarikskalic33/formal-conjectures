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
AEGIS Ω — adaptive trigram/dyadic finite-interval certificate candidate.
Generated from exact-rational Python mirror. LEAN_KERNEL_NOT_RUN.
AUTHORITY_EFFECT = NONE. No RH claim.
-/
import RHKreinCellBatchV1
import RHKreinFifteenthCellDirectV1

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinTrigramAdaptiveV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinCellBatchV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinFirstCellV1
open AEGIS.RHKreinSecondCellReductionV1

def NonnegOnQ (a b : ℚ) : Prop :=
  ∀ t : ℝ, (a : ℝ) ≤ t → t ≤ (b : ℝ) → 0 ≤ correctedExpression t

theorem nonnegOn_of_checkPiece_zero (a b : ℚ) (ha : 0 < a)
    (h : checkPiece pa19 a 0 a b = true) : NonnegOnQ a b := by
  intro t hta htb
  have hb := checkPiece_sound pa19 a 0 a b h t hta htb
  unfold Budget at hb
  simpa [correctedExpression] using hb

theorem nonnegOn_of_cellSound (c : FiniteCellV1)
    (hs : CellAnalyticSoundV1 c) (hp : (0 : ℚ) < lowerValue c) :
    NonnegOnQ c.lo c.hi := by
  intro t hlo hhi
  apply correctedExpression_nonnegative_of_normalizedExcess_v1
  have hs' := hs t hlo hhi
  have hp' : (0 : ℝ) < (lowerValue c : ℝ) := by exact_mod_cast hp
  exact hp'.le.trans hs'

theorem nonnegOn_union (a m b : ℚ)
    (hl : NonnegOnQ a m) (hr : NonnegOnQ m b) : NonnegOnQ a b := by
  intro t hat htb
  by_cases htm : t ≤ (m : ℝ)
  · exact hl t hat htm
  · exact hr t (le_of_lt (lt_of_not_ge htm)) htb

/-- First two cells reuse their existing dedicated analytic proofs. -/
theorem n0000 : NonnegOnQ 0 (75/4096) := by
  apply nonnegOn_of_cellSound firstCell AEGIS.RHKreinFifteenthCellDirectV1.first_fifteen_cells_sound.1
  norm_num [firstCell, lowerValue]

theorem n0001 : NonnegOnQ (75/4096) (225/8192) := by
  apply nonnegOn_of_cellSound secondCell AEGIS.RHKreinFifteenthCellDirectV1.first_fifteen_cells_sound.2.1
  norm_num [secondCell, lowerValue]

end AEGIS.RHKreinTrigramAdaptiveV1
