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

import RHEulerGammaSharpV1

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section

namespace AEGIS.RHKreinSixthCellReductionV1

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

def sixthCell : FiniteCellV1 :=
  ⟨675 / 16384, 375 / 8192, 185364967441091393⟩

def sixthCenter : ℝ := 1425 / 32768
def sixthRadius : ℝ := 75 / 32768

def sixthJet : ℕ → ℝ
  | 0 => 81430602793 / 200000000000
  | 1 => 6120033693 / 31250000000
  | 2 => 2267541861021 / 1000000000000
  | 3 => 91089266727 / 250000000000
  | 4 => 2090978186049 / 1000000000000
  | 5 => -50233923383 / 1000000000000
  | 6 => -49015745241 / 250000000000
  | 7 => -34698979791 / 1000000000000
  | _ => 0

def sixthJetError (_ : ℕ) : ℝ := 1 / 1000000000000
def sixthSymbolLower : ℝ := -3163405140307 / 500000000000
def sixthWeightUpper : ℝ := 286213344101281 / 4503599627370496

private def sixthLeft : ℝ := 675 / 16384

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

private theorem sixthDigammaPartialLower :
    (-718379247872759 / 200000000000000 : ℝ) ≤
      ∑ n ∈ Finset.range 24, quarterTerm sixthLeft n := by
  have h0 : (-11033526878269 / 3125000000000 : ℝ) ≤
      ∑ n ∈ Finset.range 8, quarterTerm sixthLeft n := by
    norm_num [sixthLeft, quarterTerm]
  have h1 : (-45749140284757 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 8 16, quarterTerm sixthLeft n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [sixthLeft, quarterTerm]
  have h2 : (-7709249016479 / 500000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 16 24, quarterTerm sixthLeft n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [sixthLeft, quarterTerm]
  rw [← Finset.sum_range_add_sum_Ico (quarterTerm sixthLeft)
      (show 16 ≤ 24 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm sixthLeft)
      (show 8 ≤ 16 by norm_num)]
  linarith only [h0, h1, h2]

private theorem sixthDigammaLower (t : ℝ) (hst : sixthLeft ^ 2 ≤ t ^ 2) :
    (-21007 / 5000 : ℝ) ≤
      (Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).re := by
  have hcert := digamma_sharp_lower_of_sq_le sixthLeft t 24 hst
  have hpartial := sixthDigammaPartialLower
  norm_num [sixthLeft] at hcert ⊢
  have hpartial' : (-718379247872759 / 200000000000000 : ℝ) ≤
      ∑ n ∈ Finset.range 24, quarterTerm (675 / 16384) n := by
    simpa [sixthLeft] using hpartial
  linarith only [hcert, hpartial']

private theorem sixthLogPiUpper :
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

private theorem sixthPrimeAmplitudeUpper :
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

/-- The sixth-left symbol floor remains valid at every later nonnegative
frequency; the former cell-local theorem used no upper endpoint hypothesis. -/
theorem symbol_lower_of_sixthLeft_le (t : ℝ) (hleft : (675 / 16384 : ℝ) ≤ t) :
    sixthSymbolLower ≤ symbol t := by
  have hleft' : sixthLeft ≤ t := by simpa [sixthLeft] using hleft
  have ht0 : 0 ≤ t := by
    have hleft0 : 0 ≤ sixthLeft := by norm_num [sixthLeft]
    linarith
  have hst : sixthLeft ^ 2 ≤ t ^ 2 := by
    have hleft0 : 0 ≤ sixthLeft := by norm_num [sixthLeft]
    nlinarith [mul_nonneg (sub_nonneg.mpr hleft') (add_nonneg ht0 hleft0)]
  have hd := sixthDigammaLower t hst
  have hlp := sixthLogPiUpper
  have hamp := sixthPrimeAmplitudeUpper
  have hamp0 : 0 ≤ Real.sqrt 2 * Real.log 2 :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by norm_num))
  have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one (t * Real.log 2)) hamp0
  unfold symbol archSymbol
  norm_num [sixthSymbolLower] at hd hlp hamp ⊢
  linarith only [hd, hlp, hamp, hcos]

theorem sixthCell_symbol_lower (t : ℝ)
    (hlo : (sixthCell.lo : ℝ) ≤ t) (_hhi : t ≤ (sixthCell.hi : ℝ)) :
    sixthSymbolLower ≤ symbol t := by
  apply symbol_lower_of_sixthLeft_le
  simpa [sixthCell] using hlo

/-- Exact sixth-cell reduction.  Every rational, symbol, and M8 obligation is
closed; only the eight midpoint jet enclosures remain explicit. -/
theorem sixthCell_sound_of_midpoint_jets
    (hjet : ∀ k ∈ Finset.range 8,
      |exactJetCoefficient sixthCenter k - sixthJet k| ≤ sixthJetError k) :
    CellAnalyticSoundV1 sixthCell := by
  apply cellAnalyticSound_of_symmetric_jet_box sixthCell sixthCenter sixthRadius
    sixthJet sixthJetError sixthSymbolLower sixthWeightUpper
  · norm_num [sixthRadius]
  · intro t hlo hhi
    norm_num [sixthCell, sixthCenter, sixthRadius] at hlo hhi ⊢
    rw [abs_le]
    constructor <;> linarith
  · exact hjet
  · exact sixthCell_symbol_lower
  · intro t hlo hhi
    norm_num [sixthCell, sixthWeightUpper] at hlo hhi ⊢
    have ht0 : 0 ≤ t := by linarith
    nlinarith [sq_nonneg t,
      mul_nonneg (sub_nonneg.mpr hhi)
        (add_nonneg ht0 (by norm_num : (0 : ℝ) ≤ 375 / 8192))]
  · norm_num [sixthCell, lowerValue]
  · norm_num [sixthSymbolLower]
  · norm_num [sixthCell, sixthRadius, sixthJet, sixthJetError,
      sixthSymbolLower, sixthWeightUpper, lowerValue,
      symmetricPolynomialFloor, symmetricTaylorError,
      AEGIS.RHKreinM8CertificateV1.serializedM8Q,
      Finset.sum_range_succ]

end AEGIS.RHKreinSixthCellReductionV1

#print axioms AEGIS.RHKreinSixthCellReductionV1.sixthCell_symbol_lower
#print axioms AEGIS.RHKreinSixthCellReductionV1.symbol_lower_of_sixthLeft_le
#print axioms AEGIS.RHKreinSixthCellReductionV1.sixthCell_sound_of_midpoint_jets
