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

import RHKreinCellAnalyticBridgeV1
import AEGISOverlay.RHKreinFiniteIntervalKernelV1
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# First serialized cell reduction

This file instantiates the generic M8-to-cell bridge on the actual first cell
of the 2199-cell payload. Exact arithmetic closes the cell geometry, the
degree-seven polynomial lower bound and the final weighted budget. The retained
premises are concrete even Taylor-jet coefficient enclosures; the symbol,
zeroth coefficient, and all odd coefficients are produced in this file.

The decimal rationals below are candidate Taylor coefficients.  The zeroth
and all odd coefficients are proved exact here; the second, fourth, and sixth
coefficients are proved within their rational enclosures.  No all-cells,
pointwise, or RH claim is made.

AUTHORITY_EFFECT = NONE.
-/

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section

namespace AEGIS.RHKreinFirstCellV1

open AEGIS.RHKreinCellAnalyticBridgeV1
open AEGIS.RHKreinCorrectionM8BoundV1
open AEGIS.RHKreinDigammaLowerBoundV1
open AEGIS.RHKreinDigammaMonotonicityV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinFiniteIntervalKernelV1
open AEGIS.RHKreinExplicitCorrectionV1
open AEGIS.RHKreinM8AnalyticV1
open AEGIS.RHKreinM8CertificateV1
open AEGIS.RHKreinPrimeSymbolV1
open AEGIS.RHKreinSymbolIntegrationV1

/-- The literal first entry of the committed 2199-cell payload. -/
def firstCell : FiniteCellV1 :=
  ⟨0, 75 / 4096, 114511397055347687⟩

theorem firstCell_mem : firstCell ∈ finiteCells := by
  unfold finiteCells
  exact List.mem_cons.mpr (Or.inl rfl)

def firstCenter : ℝ := 0
def firstRadius : ℝ := 75 / 4096

/-- Twelve-decimal centers for the eight normalized Taylor coefficients. -/
def firstJet : ℕ → ℝ
  | 0 => 25181386563 / 62500000000
  | 1 => 0
  | 2 => 2243764096193 / 1000000000000
  | 3 => 0
  | 4 => 2096414380799 / 1000000000000
  | 5 => 0
  | 6 => -190744442117 / 1000000000000
  | 7 => 0
  | _ => 0

def firstJetError (_ : ℕ) : ℝ := 1 / 1000000000000

/-- A decimal rational strictly below the sign-aware polynomial lower bound
for `firstJet` on this nonnegative cell. -/
def firstPolynomialLower : ℝ := 4029021849 / 10000000000

/-- The exact M8 remainder plus the eight enclosure radii used by the bridge. -/
def firstTaylorError : ℝ :=
  (serializedM8Q : ℝ) * firstRadius ^ 8 / 40320 +
    ∑ k ∈ Finset.range 8, firstJetError k * firstRadius ^ k

private theorem firstTaylorError_le :
    firstTaylorError ≤ (1001 / 1000000000 : ℝ) := by
  norm_num [firstTaylorError, firstRadius, firstJetError, serializedM8Q,
    Finset.sum_range_succ]

private theorem firstGroundBudget :
    (((75 / 4096 : ℝ) ^ 2 + 1 / 4) ^ 2) *
        (lowerValue firstCell : ℝ) ≤
      (((75 / 4096 : ℝ) ^ 2 + 1 / 4) ^ 2) *
        ((-3177232903 / 500000000 : ℝ) - 1 / 16) +
      (firstPolynomialLower - 1001 / 1000000000) := by
  norm_num [firstCell, lowerValue, firstPolynomialLower]

private theorem firstCell_cover (t : ℝ)
    (hlo : (firstCell.lo : ℝ) ≤ t) (hhi : t ≤ (firstCell.hi : ℝ)) :
    |t - firstCenter| ≤ firstRadius := by
  norm_num [firstCell, firstCenter, firstRadius] at hlo hhi ⊢
  rw [abs_le]
  constructor <;> linarith

private theorem firstPolynomialLower_le (t : ℝ)
    (hlo : (firstCell.lo : ℝ) ≤ t) (hhi : t ≤ (firstCell.hi : ℝ)) :
    firstPolynomialLower ≤ jetPolynomial7 firstJet firstCenter t := by
  have hx := firstCell_cover t hlo hhi
  have ht0 : 0 ≤ t := by norm_num [firstCell] at hlo; exact hlo
  have htr : t ≤ firstRadius := by
    norm_num [firstCell, firstRadius] at hhi ⊢
    exact hhi
  have hp6 : t ^ 6 ≤ firstRadius ^ 6 := pow_le_pow_left₀ ht0 htr 6
  have h6 := mul_le_mul_of_nonpos_left hp6
    (by norm_num [firstJet] : firstJet 6 ≤ 0)
  have h2 : 0 ≤ firstJet 2 * t ^ 2 :=
    mul_nonneg (by norm_num [firstJet]) (sq_nonneg t)
  have h4 : 0 ≤ firstJet 4 * t ^ 4 :=
    mul_nonneg (by norm_num [firstJet]) (by positivity)
  norm_num [firstPolynomialLower, firstRadius, firstCenter, firstJet,
    jetPolynomial7, Finset.sum_range_succ] at h2 h4 h6 ⊢
  linarith only [h2, h4, h6]

private theorem firstCell_weight_le (t : ℝ)
    (hlo : (firstCell.lo : ℝ) ≤ t) (hhi : t ≤ (firstCell.hi : ℝ)) :
    (t ^ 2 + 1 / 4) ^ 2 ≤
      (((75 / 4096 : ℝ) ^ 2 + 1 / 4) ^ 2) := by
  norm_num [firstCell] at hlo hhi
  nlinarith [sq_nonneg t,
    mul_nonneg (sub_nonneg.mpr hhi) (add_nonneg hlo (by norm_num : (0 : ℝ) ≤ 75 / 4096))]

/-! The 128-term endpoint is split into small exact-arithmetic blocks.  This
keeps kernel replay bounded: no single `norm_num` invocation constructs the
enormous reduced denominator of the full partial sum. -/

private theorem firstDigammaPartialLower :
    (-3644384222938337 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.range 128, quarterTerm 0 n := by
  have h0 : (-1778990475942809 / 500000000000000 : ℝ) ≤
      ∑ n ∈ Finset.range 8, quarterTerm 0 n := by
    norm_num [quarterTerm]
  have h1 : (-45751803709751 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 8 16, quarterTerm 0 n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [quarterTerm]
  have h2 : (-3083795298877 / 200000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 16 24, quarterTerm 0 n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [quarterTerm]
  have h3 : (-1935164358237 / 250000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 24 32, quarterTerm 0 n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [quarterTerm]
  have h4 : (-4654313362753 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 32 40, quarterTerm 0 n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [quarterTerm]
  have h5 : (-155349765201 / 50000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 40 48, quarterTerm 0 n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [quarterTerm]
  have h6 : (-2221295982913 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 48 56, quarterTerm 0 n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [quarterTerm]
  have h7 : (-1667071562231 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 56 64, quarterTerm 0 n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [quarterTerm]
  have h8 : (-1297262096897 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 64 72, quarterTerm 0 n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [quarterTerm]
  have h9 : (-1038219382249 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 72 80, quarterTerm 0 n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [quarterTerm]
  have h10 : (-849722915773 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 80 88, quarterTerm 0 n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [quarterTerm]
  have h11 : (-177072106951 / 250000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 88 96, quarterTerm 0 n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [quarterTerm]
  have h12 : (-599452985397 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 96 104, quarterTerm 0 n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [quarterTerm]
  have h13 : (-51391311861 / 100000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 104 112, quarterTerm 0 n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [quarterTerm]
  have h14 : (-445463229723 / 1000000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 112 120, quarterTerm 0 n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [quarterTerm]
  have h15 : (-77967009453 / 200000000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ico 120 128, quarterTerm 0 n := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [quarterTerm]
  rw [← Finset.sum_range_add_sum_Ico (quarterTerm 0) (show 120 ≤ 128 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm 0) (show 112 ≤ 120 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm 0) (show 104 ≤ 112 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm 0) (show 96 ≤ 104 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm 0) (show 88 ≤ 96 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm 0) (show 80 ≤ 88 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm 0) (show 72 ≤ 80 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm 0) (show 64 ≤ 72 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm 0) (show 56 ≤ 64 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm 0) (show 48 ≤ 56 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm 0) (show 40 ≤ 48 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm 0) (show 32 ≤ 40 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm 0) (show 24 ≤ 32 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm 0) (show 16 ≤ 24 by norm_num),
    ← Finset.sum_range_add_sum_Ico (quarterTerm 0) (show 8 ≤ 16 by norm_num)]
  linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]

private theorem firstDigammaLower (t : ℝ) :
    (-371022478788819736651 / 87723000000000000000 : ℝ) ≤
      (Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).re := by
  have hcert := digamma_quarter_certificate_lower 0 128
  have hpartial := firstDigammaPartialLower
  have hzero :
      (-371022478788819736651 / 87723000000000000000 : ℝ) ≤
        (Complex.digamma ((1 / 4 : ℂ) + ((0 : ℝ) : ℂ) * Complex.I / 2)).re := by
    norm_num at hcert ⊢
    linarith only [hcert, hpartial]
  exact hzero.trans (digamma_quarter_mono_of_sq_le 0 t (by simpa using sq_nonneg t))

private theorem firstLogPiUpper :
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
  have hsquare : (p - e) ^ 2 ≤ (Real.exp x) ^ 2 := by
    nlinarith
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

private theorem firstPrimeAmplitudeUpper :
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

/-- The symbol premise for the first cell, now produced entirely by Lean from
the proved digamma series, monotonicity, and rational transcendental bounds. -/
theorem firstCell_symbol_lower (t : ℝ) :
    (-3177232903 / 500000000 : ℝ) ≤ symbol t := by
  have hd := firstDigammaLower t
  have hlp := firstLogPiUpper
  have hamp := firstPrimeAmplitudeUpper
  have hamp0 : 0 ≤ Real.sqrt 2 * Real.log 2 :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by norm_num))
  have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one (t * Real.log 2)) hamp0
  unfold symbol archSymbol
  norm_num at hd hlp hamp ⊢
  linarith only [hd, hlp, hamp, hcos]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- At center zero the sinc/cosine expression collapses to exact rational
coefficient arithmetic, so the zeroth Taylor coefficient needs no enclosure. -/
theorem firstJet_zero_exact :
    exactJetCoefficient firstCenter 0 = firstJet 0 := by
  norm_num [exactJetCoefficient, firstCenter, firstJet, correctionSymbol,
    hatCoefficient, splineCoefficient, Fin.sum_univ_succ]

private theorem sinc_analyticAt_zero : AnalyticAt ℝ Real.sinc 0 := by
  rw [Real.sinc_eq_dslope]
  rcases Real.analyticAt_sin with ⟨p, hp⟩
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

private theorem sinc_analyticAt (x : ℝ) : AnalyticAt ℝ Real.sinc x := by
  by_cases hx : x = 0
  · simpa [hx] using sinc_analyticAt_zero
  · have hquot : AnalyticAt ℝ (fun y : ℝ => Real.sin y / y) x :=
      Real.analyticAt_sin.div analyticAt_id hx
    apply hquot.congr
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact (Real.sinc_of_ne_zero hy).symm

private theorem sinc_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n Real.sinc := by
  rw [contDiff_iff_contDiffAt]
  exact fun x => (sinc_analyticAt x).contDiffAt

private theorem odd_iteratedDeriv_zero_of_even
    (f : ℝ → ℝ) (heven : ∀ x, f (-x) = f x) (n : ℕ) :
    iteratedDeriv (2 * n + 1) f 0 = 0 := by
  have h := iteratedDeriv_comp_neg (2 * n + 1) f 0
  have heq : (fun x => f (-x)) = f := by
    funext x
    exact heven x
  rw [heq] at h
  have hsign : (-1 : ℝ) ^ (2 * n + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [hsign] at h
  norm_num at h
  linarith

private theorem deriv_zero_of_even_secondJet
    (f : ℝ → ℝ) (hf : DifferentiableAt ℝ f 0)
    (heven : ∀ x, f (-x) = f x) : deriv f 0 = 0 := by
  have hneg : HasDerivAt Neg.neg (-1) (0 : ℝ) := hasDerivAt_neg 0
  have hfnegzero : HasDerivAt f (deriv f 0) (-0) := by
    simpa only [neg_zero] using hf.hasDerivAt
  have hcomp : HasDerivAt (f ∘ Neg.neg) (deriv f 0 * (-1)) 0 :=
    hfnegzero.comp 0 hneg
  have heq : (f ∘ Neg.neg) = f := by
    funext x
    exact heven x
  rw [heq] at hcomp
  have hu := hcomp.unique hf.hasDerivAt
  linarith

private theorem sinc_first_derivative_zero : iteratedDeriv 1 Real.sinc 0 = 0 := by
  rw [iteratedDeriv_one]
  have hc : ContDiffAt ℝ 1 Real.sinc 0 := sinc_analyticAt_zero.contDiffAt
  exact deriv_zero_of_even_secondJet Real.sinc
    (hc.differentiableAt (by norm_num)) Real.sinc_neg

private theorem sinc_second_derivative_zero :
    iteratedDeriv 2 Real.sinc 0 = -(1 / 3 : ℝ) := by
  have hs : ContDiffAt ℝ 3 Real.sinc 0 := sinc_analyticAt_zero.contDiffAt
  have hid : ContDiffAt ℝ 3 (fun x : ℝ => x) 0 := contDiffAt_id
  have hmul := iteratedDeriv_mul (n := 3) hid hs
  have heq : (fun x : ℝ => x * Real.sinc x) = Real.sin := by
    funext x
    by_cases hx : x = 0
    · simp [hx]
    · rw [Real.sinc_of_ne_zero hx]
      field_simp
  change iteratedDeriv 3 (fun x : ℝ => x * Real.sinc x) 0 = _ at hmul
  rw [heq] at hmul
  norm_num [Real.iteratedDeriv_odd_sin, iteratedDeriv_fun_id,
    Finset.sum_range_succ] at hmul
  linarith

private theorem sinc_fourth_derivative_zero :
    iteratedDeriv 4 Real.sinc 0 = (1 / 5 : ℝ) := by
  have hs : ContDiffAt ℝ 5 Real.sinc 0 := sinc_analyticAt_zero.contDiffAt
  have hid : ContDiffAt ℝ 5 (fun x : ℝ => x) 0 := contDiffAt_id
  have hmul := iteratedDeriv_mul (n := 5) hid hs
  have heq : (fun x : ℝ => x * Real.sinc x) = Real.sin := by
    funext x
    by_cases hx : x = 0
    · simp [hx]
    · rw [Real.sinc_of_ne_zero hx]
      field_simp
  change iteratedDeriv 5 (fun x : ℝ => x * Real.sinc x) 0 = _ at hmul
  rw [heq] at hmul
  norm_num [Real.iteratedDeriv_odd_sin, iteratedDeriv_fun_id,
    Finset.sum_range_succ] at hmul
  linarith

private theorem sinc_sixth_derivative_zero :
    iteratedDeriv 6 Real.sinc 0 = -(1 / 7 : ℝ) := by
  have hs : ContDiffAt ℝ 7 Real.sinc 0 := sinc_analyticAt_zero.contDiffAt
  have hid : ContDiffAt ℝ 7 (fun x : ℝ => x) 0 := contDiffAt_id
  have hmul := iteratedDeriv_mul (n := 7) hid hs
  have heq : (fun x : ℝ => x * Real.sinc x) = Real.sin := by
    funext x
    by_cases hx : x = 0
    · simp [hx]
    · rw [Real.sinc_of_ne_zero hx]
      field_simp
  change iteratedDeriv 7 (fun x : ℝ => x * Real.sinc x) 0 = _ at hmul
  rw [heq] at hmul
  norm_num [Real.iteratedDeriv_odd_sin, iteratedDeriv_fun_id,
    Finset.sum_range_succ] at hmul
  linarith

private theorem scaled_sinc_second_derivative_zero (c : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => Real.sinc (c * x)) 0 = -(c ^ 2 / 3) := by
  rw [iteratedDeriv_comp_const_mul (sinc_contDiff 2) c]
  simp only [mul_zero]
  rw [sinc_second_derivative_zero]
  ring

private theorem scaled_sinc_fourth_derivative_zero (c : ℝ) :
    iteratedDeriv 4 (fun x : ℝ => Real.sinc (c * x)) 0 = c ^ 4 / 5 := by
  rw [iteratedDeriv_comp_const_mul (sinc_contDiff 4) c]
  simp only [mul_zero]
  rw [sinc_fourth_derivative_zero]
  ring

private theorem scaled_sinc_sixth_derivative_zero (c : ℝ) :
    iteratedDeriv 6 (fun x : ℝ => Real.sinc (c * x)) 0 = -(c ^ 6 / 7) := by
  rw [iteratedDeriv_comp_const_mul (sinc_contDiff 6) c]
  simp only [mul_zero]
  rw [sinc_sixth_derivative_zero]
  ring

private theorem scaled_sinc_first_derivative_zero (c : ℝ) :
    iteratedDeriv 1 (fun x : ℝ => Real.sinc (c * x)) 0 = 0 := by
  rw [iteratedDeriv_comp_const_mul (sinc_contDiff 1) c]
  simp only [mul_zero]
  rw [sinc_first_derivative_zero]
  simp

private theorem power_second_derivative_zero
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (h0 : f 0 = 1) (h1 : iteratedDeriv 1 f 0 = 0) (m : ℕ) :
    iteratedDeriv 2 (fun x => f x ^ m) 0 = m * iteratedDeriv 2 f 0 := by
  induction m with
  | zero => simp [iteratedDeriv_const]
  | succ m ih =>
      have hm := iteratedDeriv_mul (n := 2) (x := (0 : ℝ))
        (hf.pow m).contDiffAt hf.contDiffAt
      change iteratedDeriv 2 (fun x => f x ^ m * f x) 0 = _ at hm
      norm_num [Finset.sum_range_succ, h0, h1, ih] at hm
      change iteratedDeriv 2 (fun x => f x ^ m * f x) 0 = _
      rw [hm]
      push_cast
      ring

private theorem power_fourth_derivative_zero
    (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (heven : ∀ x, f (-x) = f x)
    (h0 : f 0 = 1) (m : ℕ) :
    iteratedDeriv 4 (fun x => f x ^ m) 0 =
      m * iteratedDeriv 4 f 0 +
        3 * m * (m - 1) * (iteratedDeriv 2 f 0) ^ 2 := by
  have h1 : iteratedDeriv 1 f 0 = 0 := by
    simpa using odd_iteratedDeriv_zero_of_even f heven 0
  have h3 : iteratedDeriv 3 f 0 = 0 := by
    simpa using odd_iteratedDeriv_zero_of_even f heven 1
  induction m with
  | zero => simp [iteratedDeriv_const]
  | succ m ih =>
      have hpowEven (x : ℝ) : (f (-x)) ^ m = (f x) ^ m := by rw [heven]
      have hm1 : iteratedDeriv 1 (fun x => f x ^ m) 0 = 0 := by
        simpa using odd_iteratedDeriv_zero_of_even (fun x => f x ^ m) hpowEven 0
      have hm3 : iteratedDeriv 3 (fun x => f x ^ m) 0 = 0 := by
        simpa using odd_iteratedDeriv_zero_of_even (fun x => f x ^ m) hpowEven 1
      have hm2 := power_second_derivative_zero f (hf.of_le (by norm_num)) h0 h1 m
      have hmul := iteratedDeriv_mul (n := 4) (x := (0 : ℝ))
        (hf.pow m).contDiffAt hf.contDiffAt
      change iteratedDeriv 4 (fun x => f x ^ m * f x) 0 = _ at hmul
      norm_num [Finset.sum_range_succ, h0, h1, h3, hm1, hm2, hm3] at hmul
      change iteratedDeriv 4 (fun x => f x ^ m * f x) 0 = _
      rw [hmul, ih]
      push_cast
      norm_num [Nat.choose]
      ring

private theorem power_sixth_derivative_zero
    (f : ℝ → ℝ) (hf : ContDiff ℝ 6 f) (heven : ∀ x, f (-x) = f x)
    (h0 : f 0 = 1) (m : ℕ) :
    iteratedDeriv 6 (fun x => f x ^ m) 0 =
      m * iteratedDeriv 6 f 0 +
        15 * m * (m - 1) * iteratedDeriv 4 f 0 * iteratedDeriv 2 f 0 +
        15 * m * (m - 1) * (m - 2) * (iteratedDeriv 2 f 0) ^ 3 := by
  have h1 : iteratedDeriv 1 f 0 = 0 := by
    simpa using odd_iteratedDeriv_zero_of_even f heven 0
  have h3 : iteratedDeriv 3 f 0 = 0 := by
    simpa using odd_iteratedDeriv_zero_of_even f heven 1
  have h5 : iteratedDeriv 5 f 0 = 0 := by
    simpa using odd_iteratedDeriv_zero_of_even f heven 2
  induction m with
  | zero => simp [iteratedDeriv_const]
  | succ m ih =>
      have hpowEven (x : ℝ) : (f (-x)) ^ m = (f x) ^ m := by rw [heven]
      have hm1 : iteratedDeriv 1 (fun x => f x ^ m) 0 = 0 := by
        simpa using odd_iteratedDeriv_zero_of_even (fun x => f x ^ m) hpowEven 0
      have hm3 : iteratedDeriv 3 (fun x => f x ^ m) 0 = 0 := by
        simpa using odd_iteratedDeriv_zero_of_even (fun x => f x ^ m) hpowEven 1
      have hm5 : iteratedDeriv 5 (fun x => f x ^ m) 0 = 0 := by
        simpa using odd_iteratedDeriv_zero_of_even (fun x => f x ^ m) hpowEven 2
      have hm2 := power_second_derivative_zero f (hf.of_le (by norm_num)) h0 h1 m
      have hm4 := power_fourth_derivative_zero f (hf.of_le (by norm_num)) heven h0 m
      have hmul := iteratedDeriv_mul (n := 6) (x := (0 : ℝ))
        (hf.pow m).contDiffAt hf.contDiffAt
      change iteratedDeriv 6 (fun x => f x ^ m * f x) 0 = _ at hmul
      norm_num [Finset.sum_range_succ, h0, h1, h3, h5, hm1, hm2, hm3, hm4,
        hm5, Nat.choose] at hmul
      change iteratedDeriv 6 (fun x => f x ^ m * f x) 0 = _
      rw [hmul, ih]
      push_cast
      ring

private theorem scaled_sinc_pow_second_derivative_zero (c : ℝ) (m : ℕ) :
    iteratedDeriv 2 (fun x : ℝ => Real.sinc (c * x) ^ m) 0 =
      -(m * c ^ 2 / 3) := by
  have hc : ContDiff ℝ 2 (fun x : ℝ => Real.sinc (c * x)) :=
    (sinc_contDiff 2).comp (contDiff_const.mul contDiff_id)
  rw [power_second_derivative_zero _ hc (by simp)
    (scaled_sinc_first_derivative_zero c)]
  rw [scaled_sinc_second_derivative_zero]
  ring

private theorem scaled_sinc_pow_fourth_derivative_zero (c : ℝ) (m : ℕ) :
    iteratedDeriv 4 (fun x : ℝ => Real.sinc (c * x) ^ m) 0 =
      m * c ^ 4 / 5 + m * (m - 1) * c ^ 4 / 3 := by
  let f : ℝ → ℝ := fun x => Real.sinc (c * x)
  have hf : ContDiff ℝ 4 f :=
    (sinc_contDiff 4).comp (contDiff_const.mul contDiff_id)
  have heven (x : ℝ) : f (-x) = f x := by simp [f]
  rw [power_fourth_derivative_zero f hf heven (by simp [f])]
  rw [scaled_sinc_second_derivative_zero, scaled_sinc_fourth_derivative_zero]
  ring

private theorem scaled_sinc_pow_sixth_derivative_zero (c : ℝ) (m : ℕ) :
    iteratedDeriv 6 (fun x : ℝ => Real.sinc (c * x) ^ m) 0 =
      -(m * c ^ 6 / 7) - m * (m - 1) * c ^ 6 -
        5 * m * (m - 1) * (m - 2) * c ^ 6 / 9 := by
  let f : ℝ → ℝ := fun x => Real.sinc (c * x)
  have hf : ContDiff ℝ 6 f :=
    (sinc_contDiff 6).comp (contDiff_const.mul contDiff_id)
  have heven (x : ℝ) : f (-x) = f x := by simp [f]
  rw [power_sixth_derivative_zero f hf heven (by simp [f])]
  rw [scaled_sinc_second_derivative_zero, scaled_sinc_fourth_derivative_zero,
    scaled_sinc_sixth_derivative_zero]
  ring

private theorem scaled_cos_second_derivative_zero (c : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => Real.cos (c * x)) 0 = -c ^ 2 := by
  rw [iteratedDeriv_comp_const_mul Real.contDiff_cos c]
  simp

private theorem scaled_sin_second_derivative_zero (c : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => Real.sin (c * x)) 0 = 0 := by
  rw [iteratedDeriv_comp_const_mul Real.contDiff_sin c]
  simp

private theorem scaled_cos_third_derivative_zero (c : ℝ) :
    iteratedDeriv 3 (fun x : ℝ => Real.cos (c * x)) 0 = 0 := by
  rw [iteratedDeriv_comp_const_mul Real.contDiff_cos c]
  simp

private theorem scaled_cos_fourth_derivative_zero (c : ℝ) :
    iteratedDeriv 4 (fun x : ℝ => Real.cos (c * x)) 0 = c ^ 4 := by
  rw [iteratedDeriv_comp_const_mul Real.contDiff_cos c]
  simp

private theorem scaled_sin_third_derivative_zero (c : ℝ) :
    iteratedDeriv 3 (fun x : ℝ => Real.sin (c * x)) 0 = -c ^ 3 := by
  rw [iteratedDeriv_comp_const_mul Real.contDiff_sin c]
  simp

private theorem scaled_sin_fourth_derivative_zero (c : ℝ) :
    iteratedDeriv 4 (fun x : ℝ => Real.sin (c * x)) 0 = 0 := by
  rw [iteratedDeriv_comp_const_mul Real.contDiff_sin c]
  simp

private theorem scaled_cos_fifth_derivative_zero (c : ℝ) :
    iteratedDeriv 5 (fun x : ℝ => Real.cos (c * x)) 0 = 0 := by
  rw [iteratedDeriv_comp_const_mul Real.contDiff_cos c]
  simp

private theorem scaled_cos_sixth_derivative_zero (c : ℝ) :
    iteratedDeriv 6 (fun x : ℝ => Real.cos (c * x)) 0 = -c ^ 6 := by
  rw [iteratedDeriv_comp_const_mul Real.contDiff_cos c]
  simp

private theorem scaled_sin_fifth_derivative_zero (c : ℝ) :
    iteratedDeriv 5 (fun x : ℝ => Real.sin (c * x)) 0 = c ^ 5 := by
  rw [iteratedDeriv_comp_const_mul Real.contDiff_sin c]
  simp

private theorem scaled_sin_sixth_derivative_zero (c : ℝ) :
    iteratedDeriv 6 (fun x : ℝ => Real.sin (c * x)) 0 = 0 := by
  rw [iteratedDeriv_comp_const_mul Real.contDiff_sin c]
  simp

private theorem scaled_cos_first_derivative_zero (c : ℝ) :
    iteratedDeriv 1 (fun x : ℝ => Real.cos (c * x)) 0 = 0 := by
  rw [iteratedDeriv_comp_const_mul Real.contDiff_cos c]
  simp

private theorem scaled_sin_first_derivative_zero (c : ℝ) :
    iteratedDeriv 1 (fun x : ℝ => Real.sin (c * x)) 0 = c := by
  rw [iteratedDeriv_comp_const_mul Real.contDiff_sin c]
  simp

private theorem monomial_cos_second_derivative_zero (m : ℕ) (c : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => x ^ m * Real.cos (c * x)) 0 =
      (if m = 0 then -c ^ 2 else if m = 2 then 2 else 0) := by
  have hcos : ContDiff ℝ 2 (fun x : ℝ => Real.cos (c * x)) :=
    Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)
  have hmul := iteratedDeriv_mul (n := 2) (x := (0 : ℝ))
    (contDiff_id.pow m).contDiffAt hcos.contDiffAt
  change iteratedDeriv 2 (fun x : ℝ => x ^ m * Real.cos (c * x)) 0 = _ at hmul
  rcases m with (_ | _ | _ | m)
  · norm_num [Finset.sum_range_succ, iteratedDeriv_pow,
      scaled_cos_first_derivative_zero, scaled_cos_second_derivative_zero] at hmul ⊢
  · norm_num [Finset.sum_range_succ, iteratedDeriv_pow, iteratedDeriv_fun_id_zero,
      scaled_cos_first_derivative_zero, scaled_cos_second_derivative_zero] at hmul ⊢
    linarith
  · norm_num [Finset.sum_range_succ, iteratedDeriv_pow,
      scaled_cos_first_derivative_zero, scaled_cos_second_derivative_zero] at hmul ⊢
    linarith
  · have hexp : m + 1 + 1 + 1 - 2 = m + 1 := by omega
    norm_num [Finset.sum_range_succ, iteratedDeriv_pow,
      scaled_cos_first_derivative_zero, scaled_cos_second_derivative_zero] at hmul ⊢
    rw [hexp] at hmul
    simp at hmul
    exact hmul

private theorem monomial_sin_second_derivative_zero (m : ℕ) (c : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => x ^ m * Real.sin (c * x)) 0 =
      (if m = 1 then 2 * c else 0) := by
  have hsin : ContDiff ℝ 2 (fun x : ℝ => Real.sin (c * x)) :=
    Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
  have hmul := iteratedDeriv_mul (n := 2) (x := (0 : ℝ))
    (contDiff_id.pow m).contDiffAt hsin.contDiffAt
  change iteratedDeriv 2 (fun x : ℝ => x ^ m * Real.sin (c * x)) 0 = _ at hmul
  rcases m with (_ | _ | _ | m)
  · norm_num [Finset.sum_range_succ, iteratedDeriv_pow,
      scaled_sin_first_derivative_zero, scaled_sin_second_derivative_zero] at hmul ⊢
  · norm_num [Finset.sum_range_succ, iteratedDeriv_pow, iteratedDeriv_fun_id_zero,
      scaled_sin_first_derivative_zero, scaled_sin_second_derivative_zero] at hmul ⊢
    linarith
  · norm_num [Finset.sum_range_succ, iteratedDeriv_pow,
      scaled_sin_first_derivative_zero, scaled_sin_second_derivative_zero] at hmul ⊢
    linarith
  · norm_num [Finset.sum_range_succ, iteratedDeriv_pow,
      scaled_sin_first_derivative_zero, scaled_sin_second_derivative_zero] at hmul ⊢
    exact hmul

private theorem monomial_cos_fourth_derivative_zero (m : Fin 5) (c : ℝ) :
    iteratedDeriv 4 (fun x : ℝ => x ^ m.val * Real.cos (c * x)) 0 =
      (if m.val = 0 then c ^ 4 else if m.val = 2 then -12 * c ^ 2
       else if m.val = 4 then 24 else 0) := by
  have hcos : ContDiff ℝ 4 (fun x : ℝ => Real.cos (c * x)) :=
    Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)
  have hmul := iteratedDeriv_mul (n := 4) (x := (0 : ℝ))
    (contDiff_id.pow m.val).contDiffAt hcos.contDiffAt
  change iteratedDeriv 4 (fun x : ℝ => x ^ m.val * Real.cos (c * x)) 0 = _ at hmul
  fin_cases m <;>
    norm_num [Finset.sum_range_succ, iteratedDeriv_pow, iteratedDeriv_fun_id_zero,
      scaled_cos_first_derivative_zero, scaled_cos_second_derivative_zero,
      scaled_cos_third_derivative_zero, scaled_cos_fourth_derivative_zero,
      Nat.choose] at hmul ⊢ <;>
    exact hmul

private theorem monomial_sin_fourth_derivative_zero (m : Fin 5) (c : ℝ) :
    iteratedDeriv 4 (fun x : ℝ => x ^ m.val * Real.sin (c * x)) 0 =
      (if m.val = 1 then -4 * c ^ 3 else if m.val = 3 then 24 * c else 0) := by
  have hsin : ContDiff ℝ 4 (fun x : ℝ => Real.sin (c * x)) :=
    Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
  have hmul := iteratedDeriv_mul (n := 4) (x := (0 : ℝ))
    (contDiff_id.pow m.val).contDiffAt hsin.contDiffAt
  change iteratedDeriv 4 (fun x : ℝ => x ^ m.val * Real.sin (c * x)) 0 = _ at hmul
  fin_cases m <;>
    norm_num [Finset.sum_range_succ, iteratedDeriv_pow, iteratedDeriv_fun_id_zero,
      scaled_sin_first_derivative_zero, scaled_sin_second_derivative_zero,
      scaled_sin_third_derivative_zero, scaled_sin_fourth_derivative_zero,
      Nat.choose] at hmul ⊢ <;>
    exact hmul

private theorem monomial_cos_sixth_derivative_zero (m : Fin 5) (c : ℝ) :
    iteratedDeriv 6 (fun x : ℝ => x ^ m.val * Real.cos (c * x)) 0 =
      (if m.val = 0 then -c ^ 6 else if m.val = 2 then 30 * c ^ 4
       else if m.val = 4 then -360 * c ^ 2 else 0) := by
  have hcos : ContDiff ℝ 6 (fun x : ℝ => Real.cos (c * x)) :=
    Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)
  have hmul := iteratedDeriv_mul (n := 6) (x := (0 : ℝ))
    (contDiff_id.pow m.val).contDiffAt hcos.contDiffAt
  change iteratedDeriv 6 (fun x : ℝ => x ^ m.val * Real.cos (c * x)) 0 = _ at hmul
  fin_cases m <;>
    norm_num [Finset.sum_range_succ, iteratedDeriv_pow, iteratedDeriv_fun_id_zero,
      scaled_cos_first_derivative_zero, scaled_cos_second_derivative_zero,
      scaled_cos_third_derivative_zero, scaled_cos_fourth_derivative_zero,
      scaled_cos_fifth_derivative_zero, scaled_cos_sixth_derivative_zero,
      Nat.choose] at hmul ⊢ <;>
    exact hmul

private theorem monomial_sin_sixth_derivative_zero (m : Fin 5) (c : ℝ) :
    iteratedDeriv 6 (fun x : ℝ => x ^ m.val * Real.sin (c * x)) 0 =
      (if m.val = 1 then 6 * c ^ 5 else if m.val = 3 then -120 * c ^ 3 else 0) := by
  have hsin : ContDiff ℝ 6 (fun x : ℝ => Real.sin (c * x)) :=
    Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
  have hmul := iteratedDeriv_mul (n := 6) (x := (0 : ℝ))
    (contDiff_id.pow m.val).contDiffAt hsin.contDiffAt
  change iteratedDeriv 6 (fun x : ℝ => x ^ m.val * Real.sin (c * x)) 0 = _ at hmul
  fin_cases m <;>
    norm_num [Finset.sum_range_succ, iteratedDeriv_pow, iteratedDeriv_fun_id_zero,
      scaled_sin_first_derivative_zero, scaled_sin_second_derivative_zero,
      scaled_sin_third_derivative_zero, scaled_sin_fourth_derivative_zero,
      scaled_sin_fifth_derivative_zero, scaled_sin_sixth_derivative_zero,
      Nat.choose] at hmul ⊢ <;>
    exact hmul

private def firstHatSum (t : ℝ) : ℝ :=
  ∑ j : Fin 199, (hatCoefficient j : ℝ) * Real.cos (hatCenter j * t)

private def firstSplineSum (t : ℝ) : ℝ :=
  ∑ j : Fin 5, (splineCoefficient j : ℝ) * t ^ j.val *
    (if j.val % 2 = 0 then Real.cos ((1619 / 2000) * t)
     else Real.sin ((1619 / 2000) * t))

private def firstHatFactor (t : ℝ) : ℝ := Real.sinc ((1 / 100) * t) ^ 2
private def firstSplineFactor (t : ℝ) : ℝ := Real.sinc ((1 / 2000) * t) ^ 19

private theorem firstHatSum_contDiff : ContDiff ℝ 2 firstHatSum := by
  unfold firstHatSum
  exact ContDiff.sum fun j _ => contDiff_const.mul
    (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))

private theorem firstSplineSum_contDiff : ContDiff ℝ 2 firstSplineSum := by
  unfold firstSplineSum
  apply ContDiff.sum
  intro j _
  by_cases h : j.val % 2 = 0 <;> simp only [h, if_true, if_false] <;> fun_prop

private theorem firstHatFactor_contDiff : ContDiff ℝ 2 firstHatFactor := by
  exact ((sinc_contDiff 2).comp (contDiff_const.mul contDiff_id)).pow 2

private theorem firstSplineFactor_contDiff : ContDiff ℝ 2 firstSplineFactor := by
  exact ((sinc_contDiff 2).comp (contDiff_const.mul contDiff_id)).pow 19

private theorem firstHatSum_contDiff_four : ContDiff ℝ 4 firstHatSum := by
  unfold firstHatSum
  exact ContDiff.sum fun j _ => contDiff_const.mul
    (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))

private theorem firstSplineSum_contDiff_four : ContDiff ℝ 4 firstSplineSum := by
  unfold firstSplineSum
  apply ContDiff.sum
  intro j _
  by_cases h : j.val % 2 = 0 <;> simp only [h, if_true, if_false] <;> fun_prop

private theorem firstHatFactor_contDiff_four : ContDiff ℝ 4 firstHatFactor := by
  exact ((sinc_contDiff 4).comp (contDiff_const.mul contDiff_id)).pow 2

private theorem firstSplineFactor_contDiff_four : ContDiff ℝ 4 firstSplineFactor := by
  exact ((sinc_contDiff 4).comp (contDiff_const.mul contDiff_id)).pow 19

private theorem firstHatSum_contDiff_six : ContDiff ℝ 6 firstHatSum := by
  unfold firstHatSum
  exact ContDiff.sum fun j _ => contDiff_const.mul
    (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))

private theorem firstSplineSum_contDiff_six : ContDiff ℝ 6 firstSplineSum := by
  unfold firstSplineSum
  apply ContDiff.sum
  intro j _
  by_cases h : j.val % 2 = 0 <;> simp only [h, if_true, if_false] <;> fun_prop

private theorem firstHatFactor_contDiff_six : ContDiff ℝ 6 firstHatFactor := by
  exact ((sinc_contDiff 6).comp (contDiff_const.mul contDiff_id)).pow 2

private theorem firstSplineFactor_contDiff_six : ContDiff ℝ 6 firstSplineFactor := by
  exact ((sinc_contDiff 6).comp (contDiff_const.mul contDiff_id)).pow 19

private theorem firstHatSum_even (t : ℝ) : firstHatSum (-t) = firstHatSum t := by
  unfold firstHatSum
  apply Finset.sum_congr rfl
  intro j _
  rw [show hatCenter j * -t = -(hatCenter j * t) by ring, Real.cos_neg]

private theorem firstSplineSum_even (t : ℝ) : firstSplineSum (-t) = firstSplineSum t := by
  unfold firstSplineSum
  apply Finset.sum_congr rfl
  intro j _
  fin_cases j
  · norm_num [Real.cos_neg]
  · norm_num [Real.sin_neg]
  · norm_num [Real.cos_neg]
  · norm_num [Real.sin_neg]
    ring
  · norm_num [Real.cos_neg]

private theorem firstHatFactor_even (t : ℝ) : firstHatFactor (-t) = firstHatFactor t := by
  simp [firstHatFactor]

private theorem firstSplineFactor_even (t : ℝ) :
    firstSplineFactor (-t) = firstSplineFactor t := by
  simp [firstSplineFactor]

private theorem first_zero_of_even (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (heven : ∀ t, f (-t) = f t) : iteratedDeriv 1 f 0 = 0 := by
  rw [iteratedDeriv_one]
  exact deriv_zero_of_even_secondJet f
    ((hf.differentiable (by norm_num)).differentiableAt) heven

private theorem firstHatSum_second :
    iteratedDeriv 2 firstHatSum 0 =
      ∑ j : Fin 199, -(hatCoefficient j : ℝ) * hatCenter j ^ 2 := by
  unfold firstHatSum
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [iteratedDeriv_const_mul_field, scaled_cos_second_derivative_zero]
    ring
  · intro j _
    exact (contDiff_const.mul
      (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))).contDiffAt

private theorem firstSplineSum_second :
    iteratedDeriv 2 firstSplineSum 0 =
      ∑ j : Fin 5, (splineCoefficient j : ℝ) *
        (if j.val % 2 = 0 then
          (if j.val = 0 then -((1619 / 2000 : ℝ) ^ 2)
           else if j.val = 2 then 2 else 0)
         else if j.val = 1 then 2 * (1619 / 2000 : ℝ) else 0) := by
  unfold firstSplineSum
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro j _
    simp only [mul_assoc]
    rw [iteratedDeriv_const_mul_field]
    fin_cases j
    · norm_num
      rw [scaled_cos_second_derivative_zero]
      ring
    · norm_num
      left
      convert monomial_sin_second_derivative_zero 1 (1619 / 2000) using 1 <;> norm_num
    · norm_num
      rw [monomial_cos_second_derivative_zero]
      norm_num
    · norm_num
      rw [monomial_sin_second_derivative_zero]
      norm_num
    · norm_num
      rw [monomial_cos_second_derivative_zero]
      norm_num
  · intro j _
    by_cases h : j.val % 2 = 0 <;> simp only [h, if_true, if_false] <;> fun_prop

private theorem firstHatSum_fourth :
    iteratedDeriv 4 firstHatSum 0 =
      ∑ j : Fin 199, (hatCoefficient j : ℝ) * hatCenter j ^ 4 := by
  unfold firstHatSum
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [iteratedDeriv_const_mul_field, scaled_cos_fourth_derivative_zero]
  · intro j _
    exact (contDiff_const.mul
      (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))).contDiffAt

private theorem firstSplineSum_fourth :
    iteratedDeriv 4 firstSplineSum 0 =
      ∑ j : Fin 5, (splineCoefficient j : ℝ) *
        (if j.val = 0 then (1619 / 2000 : ℝ) ^ 4
         else if j.val = 1 then -4 * (1619 / 2000 : ℝ) ^ 3
         else if j.val = 2 then -12 * (1619 / 2000 : ℝ) ^ 2
         else if j.val = 3 then 24 * (1619 / 2000 : ℝ)
         else if j.val = 4 then 24 else 0) := by
  unfold firstSplineSum
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro j _
    simp only [mul_assoc]
    rw [iteratedDeriv_const_mul_field]
    by_cases h : j.val % 2 = 0
    · simp only [h, if_true]
      rw [monomial_cos_fourth_derivative_zero j]
      fin_cases j <;> simp_all
    · simp only [h, if_false]
      rw [monomial_sin_fourth_derivative_zero j]
      fin_cases j <;> simp_all
  · intro j _
    by_cases h : j.val % 2 = 0 <;> simp only [h, if_true, if_false] <;> fun_prop

private theorem firstHatSum_sixth :
    iteratedDeriv 6 firstHatSum 0 =
      ∑ j : Fin 199, -(hatCoefficient j : ℝ) * hatCenter j ^ 6 := by
  unfold firstHatSum
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [iteratedDeriv_const_mul_field, scaled_cos_sixth_derivative_zero]
    ring
  · intro j _
    exact (contDiff_const.mul
      (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))).contDiffAt

private theorem firstSplineSum_sixth :
    iteratedDeriv 6 firstSplineSum 0 =
      ∑ j : Fin 5, (splineCoefficient j : ℝ) *
        (if j.val = 0 then -((1619 / 2000 : ℝ) ^ 6)
         else if j.val = 1 then 6 * (1619 / 2000 : ℝ) ^ 5
         else if j.val = 2 then 30 * (1619 / 2000 : ℝ) ^ 4
         else if j.val = 3 then -120 * (1619 / 2000 : ℝ) ^ 3
         else if j.val = 4 then -360 * (1619 / 2000 : ℝ) ^ 2 else 0) := by
  unfold firstSplineSum
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro j _
    simp only [mul_assoc]
    rw [iteratedDeriv_const_mul_field]
    by_cases h : j.val % 2 = 0
    · simp only [h, if_true]
      rw [monomial_cos_sixth_derivative_zero j]
      fin_cases j <;> simp_all
    · simp only [h, if_false]
      rw [monomial_sin_sixth_derivative_zero j]
      fin_cases j <;> simp_all
  · intro j _
    by_cases h : j.val % 2 = 0 <;> simp only [h, if_true, if_false] <;> fun_prop

private theorem correctionSymbol_second_formula :
    iteratedDeriv 2 correctionSymbol 0 =
      (2 / 50 : ℝ) *
        (iteratedDeriv 2 firstHatFactor 0 * firstHatSum 0 +
          iteratedDeriv 2 firstHatSum 0) +
      (iteratedDeriv 2 firstSplineFactor 0 * firstSplineSum 0 +
        iteratedDeriv 2 firstSplineSum 0) := by
  have hh := iteratedDeriv_mul (n := 2) (x := (0 : ℝ))
    firstHatFactor_contDiff.contDiffAt firstHatSum_contDiff.contDiffAt
  have hs := iteratedDeriv_mul (n := 2) (x := (0 : ℝ))
    firstSplineFactor_contDiff.contDiffAt firstSplineSum_contDiff.contDiffAt
  have hh1 := first_zero_of_even firstHatFactor firstHatFactor_contDiff firstHatFactor_even
  have hh2 := first_zero_of_even firstHatSum firstHatSum_contDiff firstHatSum_even
  have hs1 := first_zero_of_even firstSplineFactor firstSplineFactor_contDiff
    firstSplineFactor_even
  have hs2 := first_zero_of_even firstSplineSum firstSplineSum_contDiff firstSplineSum_even
  have hh0 : firstHatFactor 0 = 1 := by simp [firstHatFactor]
  have hs0 : firstSplineFactor 0 = 1 := by simp [firstSplineFactor]
  have heq : correctionSymbol = fun t =>
      (2 / 50 : ℝ) * (firstHatFactor t * firstHatSum t) +
        firstSplineFactor t * firstSplineSum t := by
    funext t
    simp [correctionSymbol, firstHatFactor, firstHatSum, firstSplineFactor,
      firstSplineSum, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  rw [heq, iteratedDeriv_fun_add]
  · rw [iteratedDeriv_const_mul_field]
    change iteratedDeriv 2 (fun t => firstHatFactor t * firstHatSum t) 0 = _ at hh
    change iteratedDeriv 2 (fun t => firstSplineFactor t * firstSplineSum t) 0 = _ at hs
    norm_num [Finset.sum_range_succ] at hh hs
    rw [iteratedDeriv_one] at hh1 hh2 hs1 hs2
    rw [hh1, hh2] at hh
    rw [hs1, hs2] at hs
    rw [hh0] at hh
    rw [hs0] at hs
    norm_num at hh hs
    rw [hh, hs]
    ring
  · exact (contDiff_const.mul
      (firstHatFactor_contDiff.mul firstHatSum_contDiff)).contDiffAt
  · exact (firstSplineFactor_contDiff.mul firstSplineSum_contDiff).contDiffAt

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem correctionSymbol_second_enclosure :
    |iteratedDeriv 2 correctionSymbol 0 / 2 -
        (2243764096193 / 1000000000000 : ℝ)| ≤
      (1 / 1000000000000 : ℝ) := by
  have hhatFactor : iteratedDeriv 2 firstHatFactor 0 =
      -(2 * (1 / 100 : ℝ) ^ 2 / 3) := by
    exact scaled_sinc_pow_second_derivative_zero (1 / 100) 2
  have hsplineFactor : iteratedDeriv 2 firstSplineFactor 0 =
      -(19 * (1 / 2000 : ℝ) ^ 2 / 3) := by
    exact scaled_sinc_pow_second_derivative_zero (1 / 2000) 19
  rw [correctionSymbol_second_formula, firstHatSum_second, firstSplineSum_second,
    hhatFactor, hsplineFactor]
  norm_num [firstHatFactor, firstSplineFactor, firstHatSum, firstSplineSum,
    hatCoefficient, splineCoefficient, hatCenter, Fin.sum_univ_succ]

/-- The normalized second Taylor coefficient lies in its serialized
twelve-decimal enclosure by exact rational kernel computation. -/
theorem firstJet_two_enclosure :
    |exactJetCoefficient firstCenter 2 - firstJet 2| ≤ firstJetError 2 := by
  simpa [exactJetCoefficient, firstCenter, firstJet, firstJetError,
    div_eq_mul_inv, mul_comm] using
    correctionSymbol_second_enclosure

private theorem product_fourth_zero_of_even
    (f g : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (hg : ContDiff ℝ 4 g)
    (hfeven : ∀ x, f (-x) = f x) (hgeven : ∀ x, g (-x) = g x) :
    iteratedDeriv 4 (fun x => f x * g x) 0 =
      iteratedDeriv 4 f 0 * g 0 +
        6 * iteratedDeriv 2 f 0 * iteratedDeriv 2 g 0 +
        f 0 * iteratedDeriv 4 g 0 := by
  have hmul := iteratedDeriv_mul (n := 4) (x := (0 : ℝ)) hf.contDiffAt hg.contDiffAt
  have hf1 : iteratedDeriv 1 f 0 = 0 := by
    simpa using odd_iteratedDeriv_zero_of_even f hfeven 0
  have hf3 : iteratedDeriv 3 f 0 = 0 := by
    simpa using odd_iteratedDeriv_zero_of_even f hfeven 1
  have hg1 : iteratedDeriv 1 g 0 = 0 := by
    simpa using odd_iteratedDeriv_zero_of_even g hgeven 0
  have hg3 : iteratedDeriv 3 g 0 = 0 := by
    simpa using odd_iteratedDeriv_zero_of_even g hgeven 1
  change iteratedDeriv 4 (fun x => f x * g x) 0 = _ at hmul
  norm_num [Finset.sum_range_succ, hf1, hf3, hg1, hg3, Nat.choose] at hmul
  rw [hmul]
  ring

private theorem correctionSymbol_fourth_formula :
    iteratedDeriv 4 correctionSymbol 0 =
      (2 / 50 : ℝ) *
        (iteratedDeriv 4 firstHatFactor 0 * firstHatSum 0 +
          6 * iteratedDeriv 2 firstHatFactor 0 * iteratedDeriv 2 firstHatSum 0 +
          iteratedDeriv 4 firstHatSum 0) +
      (iteratedDeriv 4 firstSplineFactor 0 * firstSplineSum 0 +
        6 * iteratedDeriv 2 firstSplineFactor 0 * iteratedDeriv 2 firstSplineSum 0 +
        iteratedDeriv 4 firstSplineSum 0) := by
  have hh := product_fourth_zero_of_even firstHatFactor firstHatSum
    firstHatFactor_contDiff_four firstHatSum_contDiff_four
    firstHatFactor_even firstHatSum_even
  have hs := product_fourth_zero_of_even firstSplineFactor firstSplineSum
    firstSplineFactor_contDiff_four firstSplineSum_contDiff_four
    firstSplineFactor_even firstSplineSum_even
  have hh0 : firstHatFactor 0 = 1 := by simp [firstHatFactor]
  have hs0 : firstSplineFactor 0 = 1 := by simp [firstSplineFactor]
  have heq : correctionSymbol = fun t =>
      (2 / 50 : ℝ) * (firstHatFactor t * firstHatSum t) +
        firstSplineFactor t * firstSplineSum t := by
    funext t
    simp [correctionSymbol, firstHatFactor, firstHatSum, firstSplineFactor,
      firstSplineSum, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  rw [heq, iteratedDeriv_fun_add]
  · rw [iteratedDeriv_const_mul_field]
    rw [hh0] at hh
    rw [hs0] at hs
    norm_num at hh hs
    rw [hh, hs]
  · exact (contDiff_const.mul
      (firstHatFactor_contDiff_four.mul firstHatSum_contDiff_four)).contDiffAt
  · exact (firstSplineFactor_contDiff_four.mul firstSplineSum_contDiff_four).contDiffAt

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem correctionSymbol_fourth_enclosure :
    |iteratedDeriv 4 correctionSymbol 0 / 24 -
        (2096414380799 / 1000000000000 : ℝ)| ≤
      (1 / 1000000000000 : ℝ) := by
  have hhatFactor2 : iteratedDeriv 2 firstHatFactor 0 =
      -(2 * (1 / 100 : ℝ) ^ 2 / 3) := by
    exact scaled_sinc_pow_second_derivative_zero (1 / 100) 2
  have hhatFactor4 : iteratedDeriv 4 firstHatFactor 0 =
      2 * (1 / 100 : ℝ) ^ 4 / 5 + 2 * (2 - 1) * (1 / 100 : ℝ) ^ 4 / 3 := by
    exact scaled_sinc_pow_fourth_derivative_zero (1 / 100) 2
  have hsplineFactor2 : iteratedDeriv 2 firstSplineFactor 0 =
      -(19 * (1 / 2000 : ℝ) ^ 2 / 3) := by
    exact scaled_sinc_pow_second_derivative_zero (1 / 2000) 19
  have hsplineFactor4 : iteratedDeriv 4 firstSplineFactor 0 =
      19 * (1 / 2000 : ℝ) ^ 4 / 5 +
        19 * (19 - 1) * (1 / 2000 : ℝ) ^ 4 / 3 := by
    exact scaled_sinc_pow_fourth_derivative_zero (1 / 2000) 19
  rw [correctionSymbol_fourth_formula, firstHatSum_second, firstSplineSum_second,
    firstHatSum_fourth, firstSplineSum_fourth, hhatFactor2, hhatFactor4,
    hsplineFactor2, hsplineFactor4]
  norm_num (config := { maxSteps := 1000000 })
    [firstHatFactor, firstSplineFactor, firstHatSum, firstSplineSum,
      hatCoefficient, splineCoefficient, hatCenter, Fin.sum_univ_succ]

/-- The normalized fourth Taylor coefficient lies in its serialized
twelve-decimal enclosure by exact rational kernel computation. -/
theorem firstJet_four_enclosure :
    |exactJetCoefficient firstCenter 4 - firstJet 4| ≤ firstJetError 4 := by
  simpa [exactJetCoefficient, firstCenter, firstJet, firstJetError,
    Nat.factorial, div_eq_mul_inv, mul_comm] using correctionSymbol_fourth_enclosure

private theorem product_sixth_zero_of_even
    (f g : ℝ → ℝ) (hf : ContDiff ℝ 6 f) (hg : ContDiff ℝ 6 g)
    (hfeven : ∀ x, f (-x) = f x) (hgeven : ∀ x, g (-x) = g x) :
    iteratedDeriv 6 (fun x => f x * g x) 0 =
      iteratedDeriv 6 f 0 * g 0 +
        15 * iteratedDeriv 4 f 0 * iteratedDeriv 2 g 0 +
        15 * iteratedDeriv 2 f 0 * iteratedDeriv 4 g 0 +
        f 0 * iteratedDeriv 6 g 0 := by
  have hmul := iteratedDeriv_mul (n := 6) (x := (0 : ℝ)) hf.contDiffAt hg.contDiffAt
  have hf1 : iteratedDeriv 1 f 0 = 0 := by
    simpa using odd_iteratedDeriv_zero_of_even f hfeven 0
  have hf3 : iteratedDeriv 3 f 0 = 0 := by
    simpa using odd_iteratedDeriv_zero_of_even f hfeven 1
  have hf5 : iteratedDeriv 5 f 0 = 0 := by
    simpa using odd_iteratedDeriv_zero_of_even f hfeven 2
  have hg1 : iteratedDeriv 1 g 0 = 0 := by
    simpa using odd_iteratedDeriv_zero_of_even g hgeven 0
  have hg3 : iteratedDeriv 3 g 0 = 0 := by
    simpa using odd_iteratedDeriv_zero_of_even g hgeven 1
  have hg5 : iteratedDeriv 5 g 0 = 0 := by
    simpa using odd_iteratedDeriv_zero_of_even g hgeven 2
  change iteratedDeriv 6 (fun x => f x * g x) 0 = _ at hmul
  norm_num [Finset.sum_range_succ, hf1, hf3, hf5, hg1, hg3, hg5, Nat.choose] at hmul
  rw [hmul]
  ring

private theorem correctionSymbol_sixth_formula :
    iteratedDeriv 6 correctionSymbol 0 =
      (2 / 50 : ℝ) *
        (iteratedDeriv 6 firstHatFactor 0 * firstHatSum 0 +
          15 * iteratedDeriv 4 firstHatFactor 0 * iteratedDeriv 2 firstHatSum 0 +
          15 * iteratedDeriv 2 firstHatFactor 0 * iteratedDeriv 4 firstHatSum 0 +
          iteratedDeriv 6 firstHatSum 0) +
      (iteratedDeriv 6 firstSplineFactor 0 * firstSplineSum 0 +
        15 * iteratedDeriv 4 firstSplineFactor 0 * iteratedDeriv 2 firstSplineSum 0 +
        15 * iteratedDeriv 2 firstSplineFactor 0 * iteratedDeriv 4 firstSplineSum 0 +
        iteratedDeriv 6 firstSplineSum 0) := by
  have hh := product_sixth_zero_of_even firstHatFactor firstHatSum
    firstHatFactor_contDiff_six firstHatSum_contDiff_six
    firstHatFactor_even firstHatSum_even
  have hs := product_sixth_zero_of_even firstSplineFactor firstSplineSum
    firstSplineFactor_contDiff_six firstSplineSum_contDiff_six
    firstSplineFactor_even firstSplineSum_even
  have hh0 : firstHatFactor 0 = 1 := by simp [firstHatFactor]
  have hs0 : firstSplineFactor 0 = 1 := by simp [firstSplineFactor]
  have heq : correctionSymbol = fun t =>
      (2 / 50 : ℝ) * (firstHatFactor t * firstHatSum t) +
        firstSplineFactor t * firstSplineSum t := by
    funext t
    simp [correctionSymbol, firstHatFactor, firstHatSum, firstSplineFactor,
      firstSplineSum, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  rw [heq, iteratedDeriv_fun_add]
  · rw [iteratedDeriv_const_mul_field]
    rw [hh0] at hh
    rw [hs0] at hs
    norm_num at hh hs
    rw [hh, hs]
  · exact (contDiff_const.mul
      (firstHatFactor_contDiff_six.mul firstHatSum_contDiff_six)).contDiffAt
  · exact (firstSplineFactor_contDiff_six.mul firstSplineSum_contDiff_six).contDiffAt

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem correctionSymbol_sixth_enclosure :
    |iteratedDeriv 6 correctionSymbol 0 / 720 -
        (-190744442117 / 1000000000000 : ℝ)| ≤
      (1 / 1000000000000 : ℝ) := by
  have hhatFactor2 : iteratedDeriv 2 firstHatFactor 0 =
      -(2 * (1 / 100 : ℝ) ^ 2 / 3) := by
    exact scaled_sinc_pow_second_derivative_zero (1 / 100) 2
  have hhatFactor4 : iteratedDeriv 4 firstHatFactor 0 =
      2 * (1 / 100 : ℝ) ^ 4 / 5 + 2 * (2 - 1) * (1 / 100 : ℝ) ^ 4 / 3 := by
    exact scaled_sinc_pow_fourth_derivative_zero (1 / 100) 2
  have hhatFactor6 : iteratedDeriv 6 firstHatFactor 0 =
      -(2 * (1 / 100 : ℝ) ^ 6 / 7) - 2 * (2 - 1) * (1 / 100 : ℝ) ^ 6 -
        5 * 2 * (2 - 1) * (2 - 2) * (1 / 100 : ℝ) ^ 6 / 9 := by
    exact scaled_sinc_pow_sixth_derivative_zero (1 / 100) 2
  have hsplineFactor2 : iteratedDeriv 2 firstSplineFactor 0 =
      -(19 * (1 / 2000 : ℝ) ^ 2 / 3) := by
    exact scaled_sinc_pow_second_derivative_zero (1 / 2000) 19
  have hsplineFactor4 : iteratedDeriv 4 firstSplineFactor 0 =
      19 * (1 / 2000 : ℝ) ^ 4 / 5 +
        19 * (19 - 1) * (1 / 2000 : ℝ) ^ 4 / 3 := by
    exact scaled_sinc_pow_fourth_derivative_zero (1 / 2000) 19
  have hsplineFactor6 : iteratedDeriv 6 firstSplineFactor 0 =
      -(19 * (1 / 2000 : ℝ) ^ 6 / 7) -
        19 * (19 - 1) * (1 / 2000 : ℝ) ^ 6 -
        5 * 19 * (19 - 1) * (19 - 2) * (1 / 2000 : ℝ) ^ 6 / 9 := by
    exact scaled_sinc_pow_sixth_derivative_zero (1 / 2000) 19
  rw [correctionSymbol_sixth_formula, firstHatSum_second, firstSplineSum_second,
    firstHatSum_fourth, firstSplineSum_fourth, firstHatSum_sixth,
    firstSplineSum_sixth, hhatFactor2, hhatFactor4, hhatFactor6,
    hsplineFactor2, hsplineFactor4, hsplineFactor6]
  norm_num (config := { maxSteps := 1000000 })
    [firstHatFactor, firstSplineFactor, firstHatSum, firstSplineSum,
      hatCoefficient, splineCoefficient, hatCenter, Fin.sum_univ_succ]

/-- The normalized sixth Taylor coefficient lies in its serialized
twelve-decimal enclosure by exact rational kernel computation. -/
theorem firstJet_six_enclosure :
    |exactJetCoefficient firstCenter 6 - firstJet 6| ≤ firstJetError 6 := by
  simpa [exactJetCoefficient, firstCenter, firstJet, firstJetError,
    Nat.factorial, div_eq_mul_inv, mul_comm] using correctionSymbol_sixth_enclosure

private theorem deriv_zero_of_even
    (f : ℝ → ℝ) (hf : DifferentiableAt ℝ f 0)
    (heven : ∀ x, f (-x) = f x) : deriv f 0 = 0 := by
  have hneg : HasDerivAt Neg.neg (-1) (0 : ℝ) := hasDerivAt_neg 0
  have hfnegzero : HasDerivAt f (deriv f 0) (-0) := by
    simpa only [neg_zero] using hf.hasDerivAt
  have hcomp : HasDerivAt (f ∘ Neg.neg) (deriv f 0 * (-1)) 0 :=
    hfnegzero.comp 0 hneg
  have heq : (f ∘ Neg.neg) = f := by
    funext x
    exact heven x
  rw [heq] at hcomp
  have hu := hcomp.unique hf.hasDerivAt
  linarith

private theorem deriv_odd_of_even
    (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (heven : ∀ x, f (-x) = f x) : ∀ x, deriv f (-x) = -deriv f x := by
  intro x
  have hneg : HasDerivAt Neg.neg (-1) x := hasDerivAt_neg x
  have hfneg : HasDerivAt f (deriv f (-x)) (-x) := (hf (-x)).hasDerivAt
  have hcomp : HasDerivAt (f ∘ Neg.neg) (deriv f (-x) * (-1)) x :=
    hfneg.comp x hneg
  have heq : (f ∘ Neg.neg) = f := by
    funext y
    exact heven y
  rw [heq] at hcomp
  have hu := hcomp.unique (hf x).hasDerivAt
  linarith

private theorem deriv_even_of_odd
    (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hodd : ∀ x, f (-x) = -f x) : ∀ x, deriv f (-x) = deriv f x := by
  intro x
  have hneg : HasDerivAt Neg.neg (-1) x := hasDerivAt_neg x
  have hfneg : HasDerivAt f (deriv f (-x)) (-x) := (hf (-x)).hasDerivAt
  have hcomp : HasDerivAt (f ∘ Neg.neg) (deriv f (-x) * (-1)) x :=
    hfneg.comp x hneg
  have heq : (f ∘ Neg.neg) = fun y => -f y := by
    funext y
    exact hodd y
  rw [heq] at hcomp
  have hu := hcomp.unique (hf x).hasDerivAt.neg
  linarith

/-- For an even C⁸ real function, the third, fifth, and seventh derivatives
at the origin vanish. -/
theorem odd_iteratedDerivs_zero_of_even
    (f : ℝ → ℝ) (hf : ContDiff ℝ 8 f)
    (heven : ∀ x, f (-x) = f x) :
    iteratedDeriv 3 f 0 = 0 ∧ iteratedDeriv 5 f 0 = 0 ∧
      iteratedDeriv 7 f 0 = 0 := by
  have hd (k : ℕ) (hk : k ≤ 7) : Differentiable ℝ (deriv^[k] f) := by
    have hsum : 8 - k + k = 8 := Nat.sub_add_cancel (by omega)
    have hc : ContDiff ℝ (8 - k : ℕ) (deriv^[k] f) := by
      apply ContDiff.iterate_deriv' (8 - k) k
      rw [hsum]
      exact hf
    apply hc.differentiable
    exact_mod_cast (show 8 - k ≠ 0 by omega)
  have h1 := deriv_odd_of_even f (by simpa using hd 0 (by omega)) heven
  have h2 := deriv_even_of_odd (deriv f) (by simpa using hd 1 (by omega)) h1
  have h3 := deriv_odd_of_even (deriv (deriv f))
    (by simpa [Function.iterate_succ_apply] using hd 2 (by omega)) h2
  have h4 := deriv_even_of_odd (deriv (deriv (deriv f)))
    (by simpa [Function.iterate_succ_apply] using hd 3 (by omega)) h3
  have h5 := deriv_odd_of_even (deriv (deriv (deriv (deriv f))))
    (by simpa [Function.iterate_succ_apply] using hd 4 (by omega)) h4
  have h6 := deriv_even_of_odd (deriv (deriv (deriv (deriv (deriv f)))))
    (by simpa [Function.iterate_succ_apply] using hd 5 (by omega)) h5
  have h7 := deriv_odd_of_even (deriv (deriv (deriv (deriv (deriv (deriv f))))))
    (by simpa [Function.iterate_succ_apply] using hd 6 (by omega)) h6
  have h3zero : deriv (deriv (deriv f)) 0 = 0 := by
    have h := h3 0
    norm_num at h
    linarith
  have h5zero : deriv (deriv (deriv (deriv (deriv f)))) 0 = 0 := by
    have h := h5 0
    norm_num at h
    linarith
  have h7zero : deriv (deriv (deriv (deriv (deriv (deriv (deriv f)))))) 0 = 0 := by
    have h := h7 0
    norm_num at h
    linarith
  simpa [iteratedDeriv_eq_iterate, Function.iterate_succ_apply] using
    And.intro h3zero (And.intro h5zero h7zero)

/-- Evenness and C⁸ regularity force the normalized first Taylor coefficient
at the origin to vanish exactly. -/
theorem firstJet_one_exact :
    exactJetCoefficient firstCenter 1 = firstJet 1 := by
  have hdiff : DifferentiableAt ℝ correctionSymbol 0 :=
    (correctionSymbol_contDiff_eight.differentiable (by norm_num)).differentiableAt
  have hderiv : deriv correctionSymbol 0 = 0 :=
    deriv_zero_of_even correctionSymbol hdiff correctionSymbol_even_v1
  simp [exactJetCoefficient, firstCenter, firstJet, iteratedDeriv_one, hderiv]

/-- Evenness closes the normalized third Taylor coefficient exactly. -/
theorem firstJet_three_exact :
    exactJetCoefficient firstCenter 3 = firstJet 3 := by
  have h := odd_iteratedDerivs_zero_of_even correctionSymbol
    correctionSymbol_contDiff_eight correctionSymbol_even_v1
  simp [exactJetCoefficient, firstCenter, firstJet, h.1]

/-- Evenness closes the normalized fifth Taylor coefficient exactly. -/
theorem firstJet_five_exact :
    exactJetCoefficient firstCenter 5 = firstJet 5 := by
  have h := odd_iteratedDerivs_zero_of_even correctionSymbol
    correctionSymbol_contDiff_eight correctionSymbol_even_v1
  simp [exactJetCoefficient, firstCenter, firstJet, h.2.1]

/-- Evenness closes the normalized seventh Taylor coefficient exactly. -/
theorem firstJet_seven_exact :
    exactJetCoefficient firstCenter 7 = firstJet 7 := by
  have h := odd_iteratedDerivs_zero_of_even correctionSymbol
    correctionSymbol_contDiff_eight correctionSymbol_even_v1
  simp [exactJetCoefficient, firstCenter, firstJet, h.2.2]

/-- The first real serialized cell is sound: its symbol lower bound and all
eight Taylor coefficients are kernel-produced above. -/
theorem firstCell_sound_of_jet_enclosures : CellAnalyticSoundV1 firstCell := by
  apply cellAnalyticSound_of_jet_enclosures firstCell firstCenter firstRadius
    firstPolynomialLower firstJet firstJetError
  · norm_num [firstRadius]
  · exact firstCell_cover
  · intro k hk
    by_cases hk0 : k = 0
    · subst k
      rw [firstJet_zero_exact]
      norm_num [firstJetError]
    · by_cases hk1 : k = 1
      · subst k
        rw [firstJet_one_exact]
        norm_num [firstJetError]
      · by_cases hk2 : k = 2
        · subst k
          exact firstJet_two_enclosure
        · by_cases hk3 : k = 3
          · subst k
            rw [firstJet_three_exact]
            norm_num [firstJetError]
          · by_cases hk4 : k = 4
            · subst k
              exact firstJet_four_enclosure
            · by_cases hk5 : k = 5
              · subst k
                rw [firstJet_five_exact]
                norm_num [firstJetError]
              · by_cases hk6 : k = 6
                · subst k
                  exact firstJet_six_enclosure
                · by_cases hk7 : k = 7
                  · subst k
                    rw [firstJet_seven_exact]
                    norm_num [firstJetError]
                  · simp only [Finset.mem_range] at hk
                    omega
  · exact firstPolynomialLower_le
  · intro t hlo hhi
    have hw := firstCell_weight_le t hlo hhi
    have hs := firstCell_symbol_lower t
    have hwp : 0 ≤ (t ^ 2 + 1 / 4) ^ 2 := sq_nonneg _
    have hsMul := mul_le_mul_of_nonneg_left
      (sub_le_sub_right hs (1 / 16)) hwp
    have hsNonpos : (-3177232903 / 500000000 : ℝ) - 1 / 16 ≤ 0 := by
      norm_num
    have hweightSymbol :
        (((75 / 4096 : ℝ) ^ 2 + 1 / 4) ^ 2) *
            ((-3177232903 / 500000000 : ℝ) - 1 / 16) ≤
          (t ^ 2 + 1 / 4) ^ 2 * (symbol t - 1 / 16) := by
      exact (mul_le_mul_of_nonpos_right hw hsNonpos).trans hsMul
    have hlowerNonneg : (0 : ℝ) ≤ lowerValue firstCell := by
      norm_num [firstCell, lowerValue]
    have hlowerWeight :
        (t ^ 2 + 1 / 4) ^ 2 * lowerValue firstCell ≤
          (((75 / 4096 : ℝ) ^ 2 + 1 / 4) ^ 2) * lowerValue firstCell :=
      mul_le_mul_of_nonneg_right hw hlowerNonneg
    have hground := firstGroundBudget
    have herror :
        firstPolynomialLower - 1001 / 1000000000 ≤
          firstPolynomialLower - firstTaylorError := by
      linarith [firstTaylorError_le]
    calc
      (t ^ 2 + 1 / 4) ^ 2 * lowerValue firstCell ≤
          (((75 / 4096 : ℝ) ^ 2 + 1 / 4) ^ 2) * lowerValue firstCell := hlowerWeight
      _ ≤ (((75 / 4096 : ℝ) ^ 2 + 1 / 4) ^ 2) *
            ((-3177232903 / 500000000 : ℝ) - 1 / 16) +
          (firstPolynomialLower - 1001 / 1000000000) := hground
      _ ≤ (t ^ 2 + 1 / 4) ^ 2 * (symbol t - 1 / 16) +
          (firstPolynomialLower - firstTaylorError) :=
        add_le_add hweightSymbol herror
      _ = (t ^ 2 + 1 / 4) ^ 2 * (symbol t - 1 / 16) +
          (firstPolynomialLower - ((serializedM8Q : ℝ) * firstRadius ^ 8 / 40320 +
            ∑ k ∈ Finset.range 8, firstJetError k * firstRadius ^ k)) := by
        rfl

end AEGIS.RHKreinFirstCellV1

#print axioms AEGIS.RHKreinFirstCellV1.firstCell_sound_of_jet_enclosures
#print axioms AEGIS.RHKreinFirstCellV1.firstCell_symbol_lower
#print axioms AEGIS.RHKreinFirstCellV1.firstJet_zero_exact
#print axioms AEGIS.RHKreinFirstCellV1.firstJet_one_exact
#print axioms AEGIS.RHKreinFirstCellV1.firstJet_two_enclosure
#print axioms AEGIS.RHKreinFirstCellV1.firstJet_four_enclosure
#print axioms AEGIS.RHKreinFirstCellV1.firstJet_six_enclosure
#print axioms AEGIS.RHKreinFirstCellV1.odd_iteratedDerivs_zero_of_even
#print axioms AEGIS.RHKreinFirstCellV1.firstJet_three_exact
#print axioms AEGIS.RHKreinFirstCellV1.firstJet_five_exact
#print axioms AEGIS.RHKreinFirstCellV1.firstJet_seven_exact
