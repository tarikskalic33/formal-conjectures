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

import RHKreinFourteenthCellCompositionV1

/-!
# Reduce the fifteenth serialized cell to eight exact midpoint-jet enclosures

The zero-centered Taylor budget is negative on serialized cell index 14, even
after re-anchoring the 24-term symbol certificate at its left endpoint.  This
file instead uses the exact midpoint and radius of the unchanged payload cell.
A 128-term rational digamma certificate closes the uniform symbol bound, and
all geometry, M8, weight, stored-bound, and ground-budget goals are discharged.
The only remaining assumptions are the eight displayed midpoint jet
enclosures; no admission or global RH assumption is introduced.
-/

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section

namespace AEGIS.RHKreinFifteenthCellReductionV1

open AEGIS.RHEulerGammaSharpV1
open AEGIS.RHKreinDigammaLowerBoundV1
open AEGIS.RHKreinDigammaMonotonicityV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinFiniteIntervalKernelV1
open AEGIS.RHKreinM8AnalyticV1
open AEGIS.RHKreinPrimeSymbolV1
open AEGIS.RHKreinSymbolIntegrationV1
open AEGIS.RHKreinSymmetricCellProducerV1
open AEGIS.RHKreinFourteenthCellCompositionV1

/-- The literal fifteenth entry of the unchanged committed payload. -/
def fifteenthCell : FiniteCellV1 :=
  ⟨2475 / 32768, 1275 / 16384, 292616690003685633⟩

def fifteenthCenter : ℝ := 5025 / 65536
def fifteenthRadius : ℝ := 75 / 65536

def fifteenthJet : ℕ → ℝ
  | 0 => 416165963423 / 1000000000000
  | 1 => 347860160497 / 1000000000000
  | 2 => 1158807525507 / 500000000000
  | 3 => 8015489529 / 12500000000
  | 4 => 51983766003 / 25000000000
  | 5 => -5642042579 / 62500000000
  | 6 => -207036090341 / 1000000000000
  | 7 => -7422888411 / 125000000000
  | _ => 0

def fifteenthJetError (_ : ℕ) : ℝ := 1 / 1000000000000
def fifteenthSymbolLower : ℝ := -313119 / 50000
def fifteenthWeightUpper : ℝ := 4724429978091121 / 72057594037927936

private def fifteenthLeft : ℝ := 2475 / 32768

private theorem digamma_sharp_lower_of_sq_le (s t : ℝ) (N : ℕ)
    (hst : s ^ 2 ≤ t ^ 2) :
    -(5773 / 10000 : ℝ) + (∑ n ∈ Finset.range N, quarterTerm s n) -
        (3 / 4 : ℝ) * (1 / ((N : ℝ) + 1 / 4) +
          1 / ((N : ℝ) + 1 / 4) ^ 2) ≤
      (Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).re := by
  have hs := digamma_quarter_finite_lower s N
  have hm := digamma_quarter_mono_of_sq_le s t hst
  have hg := gamma_lt_5773
  dsimp [quarterPoint] at hs
  linarith only [hs, hm, hg]

private theorem fifteenthDigammaPartialLower :
    (-3554195705385069 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.range 128, quarterTerm fifteenthLeft n := by
  have h0 : (-173390210722991 / 50000000000000 : ℝ) ≤
      ∑ n ∈ Finset.range 8, quarterTerm fifteenthLeft n := by
    norm_num [fifteenthLeft, quarterTerm]
  have h1 : (-457428517343 / 10000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 8 16, quarterTerm fifteenthLeft n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [fifteenthLeft, quarterTerm]
  have h2 : (-15417368337031 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 16 24, quarterTerm fifteenthLeft n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [fifteenthLeft, quarterTerm]
  have h3 : (-7740100980503 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 24 32, quarterTerm fifteenthLeft n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [fifteenthLeft, quarterTerm]
  have h4 : (-4654057375687 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 32 40, quarterTerm fifteenthLeft n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [fifteenthLeft, quarterTerm]
  have h5 : (-77671419533 / 25000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 40 48, quarterTerm fifteenthLeft n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [fifteenthLeft, quarterTerm]
  have h6 : (-2221212677807 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 48 56, quarterTerm fifteenthLeft n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [fifteenthLeft, quarterTerm]
  have h7 : (-104188599871 / 62500000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 56 64, quarterTerm fifteenthLeft n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [fifteenthLeft, quarterTerm]
  have h8 : (-51889006137 / 40000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 64 72, quarterTerm fifteenthLeft n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [fifteenthLeft, quarterTerm]
  have h9 : (-129774123421 / 125000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 72 80, quarterTerm fifteenthLeft n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [fifteenthLeft, quarterTerm]
  have h10 : (-424851702411 / 500000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 80 88, quarterTerm fifteenthLeft n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [fifteenthLeft, quarterTerm]
  have h11 : (-88534199949 / 125000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 88 96, quarterTerm fifteenthLeft n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [fifteenthLeft, quarterTerm]
  have h12 : (-11988829061 / 20000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 96 104, quarterTerm fifteenthLeft n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [fifteenthLeft, quarterTerm]
  have h13 : (-102780794621 / 200000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 104 112, quarterTerm fifteenthLeft n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [fifteenthLeft, quarterTerm]
  have h14 : (-55681981889 / 125000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 112 120, quarterTerm fifteenthLeft n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [fifteenthLeft, quarterTerm]
  have h15 : (-389829014191 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 120 128, quarterTerm fifteenthLeft n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [fifteenthLeft, quarterTerm]
  rw [← Finset.sum_range_add_sum_Ico (quarterTerm fifteenthLeft)
      (show 120 ≤ 128 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm fifteenthLeft)
      (show 112 ≤ 120 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm fifteenthLeft)
      (show 104 ≤ 112 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm fifteenthLeft)
      (show 96 ≤ 104 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm fifteenthLeft)
      (show 88 ≤ 96 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm fifteenthLeft)
      (show 80 ≤ 88 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm fifteenthLeft)
      (show 72 ≤ 80 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm fifteenthLeft)
      (show 64 ≤ 72 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm fifteenthLeft)
      (show 56 ≤ 64 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm fifteenthLeft)
      (show 48 ≤ 56 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm fifteenthLeft)
      (show 40 ≤ 48 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm fifteenthLeft)
      (show 32 ≤ 40 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm fifteenthLeft)
      (show 24 ≤ 32 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm fifteenthLeft)
      (show 16 ≤ 24 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm fifteenthLeft)
      (show 8 ≤ 16 by norm_num)]
  linarith only [h0, h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10, h11, h12, h13, h14, h15]

private theorem fifteenthDigammaLower (t : ℝ)
    (hst : fifteenthLeft ^ 2 ≤ t ^ 2) :
    (-413739 / 100000 : ℝ) ≤
      (Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).re := by
  have hcert := digamma_sharp_lower_of_sq_le fifteenthLeft t 128 hst
  have hpartial := fifteenthDigammaPartialLower
  norm_num [fifteenthLeft] at hcert ⊢
  have hpartial' : (-3554195705385069 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.range 128, quarterTerm (2475 / 32768) n := by
    simpa [fifteenthLeft] using hpartial
  linarith only [hcert, hpartial']

private theorem fifteenthLogPiUpper :
    Real.log Real.pi ≤ (1144729886 / 1000000000 : ℝ) := by
  let x : ℝ := (1144729886 / 2000000000 : ℝ)
  let p : ℝ := ∑ m ∈ Finset.range 16, x ^ m / m.factorial
  let e : ℝ := |x| ^ 16 * ((17 : ℝ) / (Nat.factorial 16 * 16))
  have hb := Real.exp_bound (x := x) (n := 16) (by norm_num [x]) (by norm_num)
  have hlo : p - e ≤ Real.exp x := by
    rw [abs_sub_le_iff] at hb
    dsimp [p, e]
    linarith [hb.1]
  have hp : 0 ≤ p - e := by
    norm_num [p, e, x, Finset.sum_range_succ, abs_of_nonneg]
  have hexp : 0 < Real.exp x := Real.exp_pos x
  have hsquare : (p - e) ^ 2 ≤ (Real.exp x) ^ 2 := by nlinarith
  have hpi : Real.pi ≤ (p - e) ^ 2 := by
    have h := Real.pi_lt_d20
    norm_num [p, e, x, Finset.sum_range_succ, abs_of_nonneg] at h ⊢
    linarith
  have hq : Real.exp (1144729886 / 1000000000 : ℝ) = (Real.exp x) ^ 2 := by
    rw [show (1144729886 / 1000000000 : ℝ) = x + x by norm_num [x], Real.exp_add]
    ring
  apply (Real.log_le_iff_le_exp Real.pi_pos).2
  rw [hq]
  exact hpi.trans hsquare

private theorem fifteenthPrimeAmplitudeUpper :
    Real.sqrt 2 * Real.log 2 ≤
      (1414213563 / 1000000000 : ℝ) * (6931471808 / 10000000000 : ℝ) := by
  have hs : Real.sqrt 2 ≤ (1414213563 / 1000000000 : ℝ) := by
    have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hs0 := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hl0 := (log_two_enclosure).2
  have hl : Real.log 2 ≤ (6931471808 / 10000000000 : ℝ) := by
    norm_num at hl0 ⊢
    exact hl0.le
  exact mul_le_mul hs hl (Real.log_nonneg (by norm_num)) (by norm_num)

/-- The 128-term exact certificate gives a uniform symbol floor from the
fifteenth cell's left endpoint onward. -/
theorem symbol_lower_of_fifteenthLeft_le (t : ℝ)
    (hleft : (2475 / 32768 : ℝ) ≤ t) :
    fifteenthSymbolLower ≤ symbol t := by
  have hleft' : fifteenthLeft ≤ t := by simpa [fifteenthLeft] using hleft
  have ht0 : 0 ≤ t := by
    have hleft0 : 0 ≤ fifteenthLeft := by norm_num [fifteenthLeft]
    linarith
  have hst : fifteenthLeft ^ 2 ≤ t ^ 2 := by
    have hleft0 : 0 ≤ fifteenthLeft := by norm_num [fifteenthLeft]
    nlinarith [mul_nonneg (sub_nonneg.mpr hleft') (add_nonneg ht0 hleft0)]
  have hd := fifteenthDigammaLower t hst
  have hlp := fifteenthLogPiUpper
  have hamp := fifteenthPrimeAmplitudeUpper
  have hamp0 : 0 ≤ Real.sqrt 2 * Real.log 2 :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by norm_num))
  have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one (t * Real.log 2)) hamp0
  unfold symbol archSymbol
  norm_num [fifteenthSymbolLower] at hd hlp hamp ⊢
  linarith only [hd, hlp, hamp, hcos]

theorem fifteenthCell_symbol_lower (t : ℝ)
    (hlo : (fifteenthCell.lo : ℝ) ≤ t)
    (_hhi : t ≤ (fifteenthCell.hi : ℝ)) :
    fifteenthSymbolLower ≤ symbol t := by
  apply symbol_lower_of_fifteenthLeft_le
  simpa [fifteenthCell] using hlo

/-- Exact fifteenth-cell reduction.  Every rational, symbol, geometry, and M8
obligation is closed; only the eight midpoint jet enclosures remain explicit. -/
theorem fifteenthCell_sound_of_midpoint_jets
    (hjet : ∀ k ∈ Finset.range 8,
      |exactJetCoefficient fifteenthCenter k - fifteenthJet k| ≤
        fifteenthJetError k) :
    CellAnalyticSoundV1 fifteenthCell := by
  apply cellAnalyticSound_of_symmetric_jet_box fifteenthCell
    fifteenthCenter fifteenthRadius fifteenthJet fifteenthJetError
    fifteenthSymbolLower fifteenthWeightUpper
  · norm_num [fifteenthRadius]
  · intro t hlo hhi
    norm_num [fifteenthCell, fifteenthCenter, fifteenthRadius] at hlo hhi ⊢
    rw [abs_le]
    constructor <;> linarith
  · exact hjet
  · exact fifteenthCell_symbol_lower
  · intro t hlo hhi
    norm_num [fifteenthCell, fifteenthWeightUpper] at hlo hhi ⊢
    have ht0 : 0 ≤ t := by linarith
    nlinarith [sq_nonneg t,
      mul_nonneg (sub_nonneg.mpr hhi)
        (add_nonneg ht0 (by norm_num : (0 : ℝ) ≤ 1275 / 16384))]
  · norm_num [fifteenthCell, lowerValue]
  · norm_num [fifteenthSymbolLower]
  · norm_num [fifteenthCell, fifteenthRadius, fifteenthJet,
      fifteenthJetError, fifteenthSymbolLower, fifteenthWeightUpper,
      lowerValue, symmetricPolynomialFloor, symmetricTaylorError,
      AEGIS.RHKreinM8CertificateV1.serializedM8Q,
      Finset.sum_range_succ]

/-- The previous fourteen premise-free results and the exact fifteenth-cell
reduction compose without weakening any theorem statement. -/
theorem first_fifteen_cells_sound_of_midpoint_jets
    (hjet : ∀ k ∈ Finset.range 8,
      |exactJetCoefficient fifteenthCenter k - fifteenthJet k| ≤
        fifteenthJetError k) :
    CellAnalyticSoundV1 AEGIS.RHKreinFirstCellV1.firstCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinSecondCellReductionV1.secondCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinThirdCellCompositionV1.thirdCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinFourthCellCompositionV1.fourthCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinFifthCellCompositionV1.fifthCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinSixthCellReductionV1.sixthCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinSeventhCellCompositionV1.seventhCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinEighthCellCompositionV1.eighthCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinNinthCellCompositionV1.ninthCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinTenthCellCompositionV1.tenthCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinEleventhCellCompositionV1.eleventhCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinTwelfthCellCompositionV1.twelfthCell ∧
      CellAnalyticSoundV1 AEGIS.RHKreinThirteenthCellCompositionV1.thirteenthCell ∧
      CellAnalyticSoundV1 fourteenthCell ∧ CellAnalyticSoundV1 fifteenthCell :=
  ⟨first_fourteen_cells_sound.1, first_fourteen_cells_sound.2.1,
    first_fourteen_cells_sound.2.2.1, first_fourteen_cells_sound.2.2.2.1,
    first_fourteen_cells_sound.2.2.2.2.1,
    first_fourteen_cells_sound.2.2.2.2.2.1,
    first_fourteen_cells_sound.2.2.2.2.2.2.1,
    first_fourteen_cells_sound.2.2.2.2.2.2.2.1,
    first_fourteen_cells_sound.2.2.2.2.2.2.2.2.1,
    first_fourteen_cells_sound.2.2.2.2.2.2.2.2.2.1,
    first_fourteen_cells_sound.2.2.2.2.2.2.2.2.2.2.1,
    first_fourteen_cells_sound.2.2.2.2.2.2.2.2.2.2.2.1,
    first_fourteen_cells_sound.2.2.2.2.2.2.2.2.2.2.2.2.1,
    first_fourteen_cells_sound.2.2.2.2.2.2.2.2.2.2.2.2.2,
    fifteenthCell_sound_of_midpoint_jets hjet⟩

end AEGIS.RHKreinFifteenthCellReductionV1

#print axioms AEGIS.RHKreinFifteenthCellReductionV1.symbol_lower_of_fifteenthLeft_le
#print axioms AEGIS.RHKreinFifteenthCellReductionV1.fifteenthCell_sound_of_midpoint_jets
#print axioms AEGIS.RHKreinFifteenthCellReductionV1.first_fifteen_cells_sound_of_midpoint_jets
