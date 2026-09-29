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
import AEGISOverlay.RHKreinCorrectionM8BoundV1

/-!
# Finite-window eighth-derivative majorant for the actual correction symbol

This keeps the existing coefficients and Fourier convention. On |t| <= T,
Leibniz differentiation of t^j times the undifferentiated spline transform
replaces the global 2000^j cost by an exact degree-j polynomial in T.
No finite-cell soundness, pointwise positivity or RH is asserted.
AUTHORITY_EFFECT = NONE.
-/
open Set MeasureTheory Complex FourierTransform
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AEGIS.RHKreinM8FiniteWindowV1
open AEGIS.RHKreinExplicitCorrectionV1 AEGIS.RHKreinM8CertificateV1
open AEGIS.RHKreinCorrectionM8BoundV1 AEGIS.RHKreinFourierTaylorBoundV1
open AEGIS.RHKreinSplineSupportV1 AEGIS.RHKreinSplineContinuityV1
open AEGIS.RHKreinSplineL1NormV1 AEGIS.RHKreinSplineDerivativesV1

/-- The fixed right support endpoint of the certificate's spline. -/
def radius : ℝ := 819 / 1000

def baseSpline : ℝ → ℂ := spline19 (4 / 5) (1 / 1000)
def splineFourier : ℝ → ℂ := angularFourier baseSpline

private theorem base_moments : HasMomentsUpToEight baseSpline :=
  hasMomentsUpToEight_of_continuous_compact _
    (spline19_continuous _ (by norm_num)) (spline19_hasCompactSupport _ _)

private theorem splineFourier_contDiff : ContDiff ℝ 8 splineFourier :=
  (fourier_contDiff_eight _ base_moments).comp (contDiff_const.mul contDiff_id)

/-- Exact angular normalization for every derivative order consumed by Leibniz. -/
theorem angular_derivative_norm_le_moment (f : ℝ → ℂ) (hf : HasMomentsUpToEight f)
    (n : ℕ) (hn : n ≤ 8) (t : ℝ) :
    ‖iteratedDeriv n (angularFourier f) t‖ ≤ ∫ x : ℝ, |x| ^ n * ‖f x‖ := by
  have hc : ContDiff ℝ n (𝓕 f) :=
    (fourier_contDiff_eight f hf).of_le (by exact_mod_cast hn)
  have hd : iteratedDeriv n (𝓕 f) =
      𝓕 (fun x : ℝ => (-2 * Real.pi * Complex.I * (x : ℂ)) ^ n • f x) := by
    apply Real.iteratedDeriv_fourier (N := (8 : ℕ∞))
    · intro k hk
      exact hf k (by exact_mod_cast hk)
    · exact_mod_cast hn
  have he : iteratedDeriv n (angularFourier f) = fun t =>
      angularScale ^ n •
        𝓕 (fun x : ℝ => (-2 * Real.pi * Complex.I * (x : ℂ)) ^ n • f x)
          (angularScale * t) := by
    unfold angularFourier
    rw [iteratedDeriv_comp_const_smul hc angularScale, hd]
  have hm (x : ℝ) : ‖((-2 * Real.pi * Complex.I * (x : ℂ)) ^ n) • f x‖ =
      (2 * Real.pi) ^ n * (|x| ^ n * ‖f x‖) := by
    norm_num [norm_smul, norm_pow, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_pow]
    ring
  have hs : |angularScale| ^ n * (2 * Real.pi) ^ n = 1 := by
    rw [← mul_pow]
    have h : |angularScale| * (2 * Real.pi) = 1 := by
      simp only [angularScale, abs_neg, abs_inv,
        abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      exact inv_mul_cancel₀ (by positivity)
    rw [h, one_pow]
  rw [he, norm_smul, Real.norm_eq_abs, abs_pow]
  calc
    _ ≤ |angularScale| ^ n * ∫ x : ℝ,
        ‖((-2 * Real.pi * Complex.I * (x : ℂ)) ^ n) • f x‖ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact VectorFourier.norm_fourierIntegral_le_integral_norm
        Real.fourierChar volume (innerₗ ℝ) _ _
    _ = ∫ x : ℝ, |x| ^ n * ‖f x‖ := by
      simp_rw [hm]
      rw [integral_const_mul, ← mul_assoc, hs, one_mul]

/-- The undifferentiated spline transform costs only radius^n at order n. -/
theorem splineFourier_derivative_le (n : ℕ) (hn : n ≤ 8) (t : ℝ) :
    ‖iteratedDeriv n splineFourier t‖ ≤ radius ^ n := by
  have hi : Integrable baseSpline := spline19_integrable _ _
  have hw : Integrable (fun x : ℝ => |x| ^ n * ‖baseSpline x‖) := by
    simpa only [Real.norm_eq_abs] using norm_moment_integrable _ base_moments n hn
  have hb (x : ℝ) : |x| ^ n * ‖baseSpline x‖ ≤ radius ^ n * ‖baseSpline x‖ := by
    by_cases hz : baseSpline x = 0
    · simp [hz]
    · have hx := spline19_support (4 / 5) (1 / 1000) x hz
      have hx0 : 0 ≤ x := by linarith [hx.1]
      have hxR : x ≤ radius := by dsimp [radius]; norm_num at hx ⊢; linarith [hx.2]
      rw [abs_of_nonneg hx0]
      gcongr
  have hmass : (∫ x : ℝ, ‖baseSpline x‖) ≤ 1 := by
    simpa [baseSpline] using
      (spline19_derivative_L1 (4 / 5) (h := 1 / 1000) (by norm_num) 0 (by norm_num)).2
  calc
    ‖iteratedDeriv n splineFourier t‖ ≤ ∫ x : ℝ, |x| ^ n * ‖baseSpline x‖ :=
      angular_derivative_norm_le_moment _ base_moments n hn t
    _ ≤ ∫ x : ℝ, radius ^ n * ‖baseSpline x‖ := integral_mono hw (hi.norm.const_mul _) hb
    _ = radius ^ n * ∫ x : ℝ, ‖baseSpline x‖ := integral_const_mul _ _
    _ ≤ radius ^ n * 1 := mul_le_mul_of_nonneg_left hmass (by unfold radius; positivity)
    _ = radius ^ n := mul_one _

private theorem complex_monomial_derivative (j k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun x : ℝ => (x : ℂ) ^ j) t =
      (j.descFactorial k : ℂ) * (t : ℂ) ^ (j - k) := by
  have hc : ContDiff ℝ k (fun x : ℝ => x ^ j) := by fun_prop
  have he : (fun x : ℝ => (x : ℂ) ^ j) =
      Complex.ofRealCLM ∘ (fun x : ℝ => x ^ j) := by ext x; simp
  rw [he]
  change iteratedFDeriv ℝ k (Complex.ofRealCLM ∘ (fun x : ℝ => x ^ j)) t
    (fun _ => 1) = _
  rw [Complex.ofRealCLM.iteratedFDeriv_comp_left hc.contDiffAt le_rfl]
  change ((iteratedDeriv k (fun x : ℝ => x ^ j) t : ℝ) : ℂ) = _
  rw [iteratedDeriv_pow]
  push_cast

/-- Exact Leibniz polynomial; descending factorials make k > j terms zero. -/
def edgeBudget (j : ℕ) (T : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 9,
    (Nat.choose 8 k : ℝ) * (j.descFactorial k : ℝ) * T ^ (j - k) * radius ^ (8 - k)

/-- The polynomial-times-transform bound before taking real parts or phases. -/
theorem monomial_spline_eighth_le (j : ℕ) (T t : ℝ) (hT : 0 ≤ T) (ht : |t| ≤ T) :
    ‖iteratedDeriv 8 (fun t : ℝ => (t : ℂ) ^ j * splineFourier t) t‖ ≤ edgeBudget j T := by
  rw [iteratedDeriv_fun_mul (by fun_prop) splineFourier_contDiff.contDiffAt]
  apply (norm_sum_le _ _).trans
  unfold edgeBudget
  apply Finset.sum_le_sum
  intro k hk
  have hnorm : ‖iteratedDeriv k (fun x : ℝ => (x : ℂ) ^ j) t‖ =
      (j.descFactorial k : ℝ) * |t| ^ (j - k) := by
    rw [complex_monomial_derivative]
    simp only [norm_mul, norm_pow, norm_natCast, Complex.norm_real, Real.norm_eq_abs]
  simp only [norm_mul, norm_natCast, hnorm]
  have hF := splineFourier_derivative_le (8 - k) (by omega) t
  have hpow : |t| ^ (j - k) ≤ T ^ (j - k) := pow_le_pow_left₀ (abs_nonneg t) ht _
  have hR : 0 ≤ radius ^ (8 - k) := by unfold radius; positivity
  calc
    _ ≤ (Nat.choose 8 k : ℝ) * ((j.descFactorial k : ℝ) * T ^ (j - k)) *
        radius ^ (8 - k) := by gcongr
    _ = _ := by ring

private theorem edge_angular (j : Fin 5) :
    angularFourier (edgePacket j) = fun t : ℝ =>
      (-Complex.I) ^ j.val * ((t : ℂ) ^ j.val * splineFourier t) := by
  funext t
  unfold angularFourier edgePacket splineFourier baseSpline
  rw [angularScale_mul, spline19_derivative_fourier _ (by norm_num) _ (by omega),
    spline19_fourier _ (by norm_num)]
  rw [mul_pow]
  ring

private theorem edge_angular_contDiff (j : Fin 5) :
    ContDiff ℝ 8 (angularFourier (edgePacket j)) := by
  rw [edge_angular]
  have hp : ContDiff ℝ 8 (fun t : ℝ => (t : ℂ) ^ j.val) := by fun_prop
  exact contDiff_const.mul (hp.mul splineFourier_contDiff)

/-- Exact unit-modulus phases are harmless; no extra factor two is introduced. -/
theorem edge_real_eighth_le (j : Fin 5) (T t : ℝ) (hT : 0 ≤ T) (ht : |t| ≤ T) :
    |iteratedDeriv 8 (realAngular (edgePacket j)) t| ≤ edgeBudget j.val T := by
  have hc := edge_angular_contDiff j
  have he : iteratedDeriv 8 (realAngular (edgePacket j)) t =
      (iteratedDeriv 8 (angularFourier (edgePacket j)) t).re := by
    change iteratedFDeriv ℝ 8 (Complex.reCLM ∘ angularFourier (edgePacket j)) t
      (fun _ => 1) = _
    rw [Complex.reCLM.iteratedFDeriv_comp_left hc.contDiffAt (by norm_num)]
    rfl
  rw [he]
  apply (Complex.abs_re_le_norm _).trans
  rw [edge_angular, iteratedDeriv_const_mul_field, norm_mul, norm_pow]
  simp only [norm_neg, Complex.norm_I, one_pow, one_mul]
  exact monomial_spline_eighth_le j.val T t hT ht

private theorem sum_eighth_bound {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (a B : ι → ℝ) (hc : ∀ i, ContDiff ℝ 8 (f i))
    (t : ℝ) (hb : ∀ i, |iteratedDeriv 8 (f i) t| ≤ B i) :
    |iteratedDeriv 8 (fun t => ∑ i, a i * f i t) t| ≤ ∑ i, |a i| * B i := by
  rw [iteratedDeriv_fun_sum (fun i _ => (contDiff_const.mul (hc i)).contDiffAt)]
  simp_rw [iteratedDeriv_const_mul_field]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hb i) (abs_nonneg _)

/-- Existing hat budget plus the improved finite-window spline budget. -/
def finiteM8 (T : ℝ) : ℝ :=
  (∑ j : Fin 199, 2 * (1 / 50) * |(hatCoefficient j : ℝ)| *
    (hatCenter j + 1 / 50) ^ 8) +
  ∑ j : Fin 5, |(splineCoefficient j : ℝ)| * edgeBudget j.val T

/-- Unconditional finite-window bound for the actual, unchanged correctionSymbol. -/
theorem correctionSymbol_eighth_le_finiteWindow (T t : ℝ) (hT : 0 ≤ T) (ht : |t| ≤ T) :
    |iteratedDeriv 8 correctionSymbol t| ≤ finiteM8 T := by
  have hm (j : Fin 199) : HasMomentsUpToEight (hatPacket j) :=
    hasMomentsUpToEight_of_continuous_compact _ (hatPacket_continuous j) (hatPacket_compact j)
  have ch (j : Fin 199) := realAngular_contDiff _ (hm j)
  have ce (j : Fin 5) : ContDiff ℝ 8 (realAngular (edgePacket j)) :=
    Complex.reCLM.contDiff.comp (edge_angular_contDiff j)
  have bh (j : Fin 199) : |iteratedDeriv 8 (realAngular (hatPacket j)) t| ≤
      (1 / 50) * (hatCenter j + 1 / 50) ^ 8 :=
    (realAngular_eighth_le_moment _ (hm j) t).trans (hatPacket_weighted_eighth_L1 j).2
  rw [correctionSymbol_eq_columns,
    iteratedDeriv_fun_add (ContDiff.sum (fun j _ => contDiff_const.mul (ch j))).contDiffAt
      (ContDiff.sum (fun j _ => contDiff_const.mul (ce j))).contDiffAt]
  apply (abs_add_le _ _).trans
  refine (add_le_add (sum_eighth_bound _ _ _ ch t bh)
    (sum_eighth_bound _ _ _ ce t (fun j => edge_real_eighth_le j T t hT ht))).trans_eq ?_
  unfold finiteM8
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    rw [abs_mul]
    norm_num
    ring
  · apply Finset.sum_congr rfl
    intro j _
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]

/-- Exact finite-window rational, with the hat sum eliminated via the proved global identity. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
theorem finiteM8_three_hundred_eq :
    finiteM8 300 =
      (138411104278141883145249511099127907904956837 /
        5000000000000000000000000000000000 : ℝ) := by
  have he : finiteM8 300 = m8Real -
      (∑ j : Fin 5, |(splineCoefficient j : ℝ)| * 2000 ^ j.val * (819 / 1000) ^ 8) +
      ∑ j : Fin 5, |(splineCoefficient j : ℝ)| * edgeBudget j.val 300 := by
    unfold finiteM8 m8Real
    ring
  rw [he, m8Real_eq_certificateM8Q, certificateM8_eq_serialized_v1]
  norm_num [serializedM8Q, splineCoefficient, edgeBudget, radius,
    Fin.sum_univ_succ, Finset.sum_range_succ, Nat.descFactorial]

/-- The 300-window majorant is rigorously over 115 times smaller than the global one. -/
theorem finiteM8_improvement_factor :
    115 * finiteM8 300 < (serializedM8Q : ℝ) ∧
      (serializedM8Q : ℝ) < 116 * finiteM8 300 := by
  rw [finiteM8_three_hundred_eq]
  norm_num [serializedM8Q]

theorem correctionSymbol_eighth_le_window300 (t : ℝ) (ht : |t| ≤ 300) :
    |iteratedDeriv 8 correctionSymbol t| ≤
      (138411104278141883145249511099127907904956837 /
        5000000000000000000000000000000000 : ℝ) := by
  simpa only [finiteM8_three_hundred_eq] using
    correctionSymbol_eighth_le_finiteWindow 300 t (by norm_num) ht

end AEGIS.RHKreinM8FiniteWindowV1
#print axioms AEGIS.RHKreinM8FiniteWindowV1.angular_derivative_norm_le_moment
#print axioms AEGIS.RHKreinM8FiniteWindowV1.splineFourier_derivative_le
#print axioms AEGIS.RHKreinM8FiniteWindowV1.monomial_spline_eighth_le
#print axioms AEGIS.RHKreinM8FiniteWindowV1.edge_real_eighth_le
#print axioms AEGIS.RHKreinM8FiniteWindowV1.correctionSymbol_eighth_le_finiteWindow
#print axioms AEGIS.RHKreinM8FiniteWindowV1.finiteM8_three_hundred_eq
#print axioms AEGIS.RHKreinM8FiniteWindowV1.finiteM8_improvement_factor
#print axioms AEGIS.RHKreinM8FiniteWindowV1.correctionSymbol_eighth_le_window300
