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

import CvSMomentTraceV1
import CvSWindowCertV1

/-!
# Finite CvS low space with moment-augmented trace
The original finite low-block (139 atoms), exact row and cross/Schur budgets
stay unchanged. Only the independent trial-distance space gains the two
exponential moments already orthogonal to any moment-zero complement.
Both pointwise Krein and augmented trial trace integrals remain hypotheses.
No unconditional RH claim.
-/
open MeasureTheory FourierTransform Complex Set Filter
open scoped ComplexConjugate InnerProductSpace ContDiff
noncomputable section
namespace AEGIS.CvSMomentWindowBridgeV1
open AEGIS.CvSFeshbachWindowV1 AEGIS.CvSWindowCertV1 AEGIS.CvSRingBridgeV1
open AEGIS.CvSMomentTraceV1 AEGIS.CvSRoughV1 AEGIS.CvSTraceV1
open AEGIS.CvSPlancherelRoughV1 AEGIS.CvSKreinRoughV1
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3
open AEGIS.WeilCriticalLineKreinFormV1 AEGIS.RHDyadicDiagonalV13

/-- The old admissible complement is automatically orthogonal to the augmented
trace functions; the low basis and its actual source rows are unchanged. -/
theorem admissible_augmented_orthogonal {p : ℕ} {LT : ℝ}
    {U : Fin p → ℝ → ℂ} {w : ℝ → ℂ}
    (hw : Admissible LT U w) :
    ∀ i : Fin (p + 2),
      (∫ x in Icc (0 : ℝ) LT, w x * conj (augment U i x)) = 0 := by
  rcases hw with ⟨_hwi, _hbound, hsupp, hmom, horth, _hE⟩
  exact augment_orthogonal hsupp hmom horth

/-- Feshbach sign with unchanged low and mixed Schur data, but augmented trace. -/
theorem window_nonneg_of_augmented_trace (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (r a : ℝ) (hw : HalfWidthAt g r a) (M : ℕ) (hM : 2 * r < Real.log ((M + 1 : ℕ) : ℝ))
    (L m : ℝ) (s : ℝ → ℝ) (hsm : Measurable s) (B : ℝ) (hsB : ∀ t, |s t| ≤ B)
    (hs0 : ∀ t, 0 ≤ s t)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (𝓕 (H i))) (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (ScertM M t - m) + (∑ i, 𝓕 (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re + Wt t * s t)
    (v w : ℝ → ℂ) (hdec : Gm g = fun u => v u + w u) (hv : Integrable v) (hwi : Integrable w)
    {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) {lo hi : ℝ} (hlh : lo ≤ hi)
    (hsupp : Function.support w ⊆ Icc lo hi) (hlen : hi - lo < L) (hmomw : MomentZero w)
    (hEw : Integrable (energy w))
    (hSv : Integrable fun t => ScertM M t * energy v t)
    (hSw : Integrable fun t => ScertM M t * energy w t)
    {p : ℕ} (U : Fin p → ℝ → ℂ) (hU : ∀ i, Continuous (U i))
    (horth : ∀ i, ∫ x in Icc lo hi, w x * conj (U i x) = 0)
    (cf : ℝ → Fin (p + 2) → ℂ) (hR : Integrable fun t => s t * trialDist lo hi (augment U) cf t)
    {T : ℝ} (hT : ∫ t, s t * trialDist lo hi (augment U) cf t ≤ T) (hcpos : 0 < m - T / (2 * Real.pi))
    {K : ℝ} (hK : 0 ≤ K)
    (hcross : (∫ t, ScertM M t * cross v w t) ^ 2 ≤ K * ∫ t, energy w t)
    (hlow : K / (m - T / (2 * Real.pi)) ≤ ∫ t, ScertM M t * energy v t) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re :=
  window_nonneg g hm r a hw M hM v w hdec hv hwi hSv hSw hcpos hK
    (complement_bound_with_moments M L m s hsm B hsB hs0 H hHc hHi hFH hHs d j hcert hwi hC hlh hsupp hlen
      hmomw hEw hSw U hU horth cf hR hT)
    hcross hlow

/-! An unchanged low-block projection with a genuinely augmented complementary
trace. This theorem is copied exactly from the proven window_of_certificate
source except for its trace trial dimension and use of the green
complement_bound_with_moments lemma. The original source remains untouched. -/
theorem window_of_certificate_augmented_trace (M : ℕ) (L LT m : ℝ) (hLT0 : 0 ≤ LT) (hLTL : LT < L)
    (hLTM : LT < Real.log ((M + 1 : ℕ) : ℝ))
    (s : ℝ → ℝ) (hsm : Measurable s) (B : ℝ) (hsB : ∀ t, |s t| ≤ B) (hs0 : ∀ t, 0 ≤ s t)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (𝓕 (H i))) (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (ScertM M t - m) + (∑ i, 𝓕 (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re + Wt t * s t)
    {p : ℕ} (U : Fin p → ℝ → ℂ) (hU : ∀ i, Continuous (U i))
    (hUmom : ∀ i, MomentZero (Set.indicator (Icc 0 LT) (U i)))
    (cf : ℝ → Fin (p + 2) → ℂ) (hR : Integrable fun t => s t * trialDist 0 LT (augment U) cf t)
    {T : ℝ} (hT : ∫ t, s t * trialDist 0 LT (augment U) cf t ≤ T) (hcpos : 0 < m - T / (2 * Real.pi))
    (hEU : ∀ c, Integrable (energy (lowBlock LT U c)))
    (hSU : ∀ c, Integrable fun t => ScertM M t * energy (lowBlock LT U c) t)
    (K : (Fin p → ℂ) → ℝ) (hK : ∀ c, 0 ≤ K c)
    (hcross : ∀ c w, Admissible LT U w →
      (∫ t, ScertM M t * cross (lowBlock LT U c) w t) ^ 2 ≤ K c * ∫ t, energy w t)
    (hlow : ∀ c, K c / (m - T / (2 * Real.pi)) ≤ ∫ t, ScertM M t * energy (lowBlock LT U c) t)
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (r a : ℝ)
    (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ LT) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  -- move the packet to `[0, 2r]`
  set lo := -a - r with hlo
  set G0 : ℝ → ℂ := fun u => Gm g (u + lo) with hG0def
  have hG0cd : ContDiff ℝ ∞ G0 := (Gm_contDiff g).comp (contDiff_id.add contDiff_const)
  have hG0c : Continuous G0 := hG0cd.continuous
  have hts := Gm_tsupport g r a hw
  have hG0s : Function.support G0 ⊆ Icc 0 LT := fun u hu => by
    have h1 : u + lo ∈ Icc (-a - r) (-a + r) := hts (subset_tsupport _ hu)
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  have hG0cs : HasCompactSupport G0 :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hG0s
  have hG0i : Integrable G0 := hG0c.integrable_of_hasCompactSupport hG0cs
  obtain ⟨CG, hCG⟩ := hG0c.bounded_above_of_compact_support hG0cs
  have hG0mom : MomentZero G0 := momentZero_translate (gm_momentZero g hm) lo
  have hEG : ∀ t, energy G0 t = energy (Gm g) t := fun t => energy_translate (Gm g) lo t
  have hEG0 : Integrable (energy G0) :=
    (fourier_normSq_integrable hG0cd hG0cs).comp_div (by positivity : (2 * Real.pi) ≠ 0)
  have hSG0 : Integrable fun t => ScertM M t * energy G0 t := by
    refine (scertMNr_integrable M g).congr (Eventually.of_forall fun t => ?_)
    show ScertM M t * Nr g t = ScertM M t * energy G0 t
    rw [hEG, Nr_eq]
    rfl
  -- the projection onto the low block
  obtain ⟨c, hc⟩ := exists_orth_coeffs (μ := volume.restrict (Icc 0 LT))
    (memLp_of_bound hG0c.aestronglyMeasurable hCG) (fun i => memLp_of_continuous (hU i))
  set v := lowBlock LT U c with hv
  set w : ℝ → ℂ := fun x => G0 x - v x with hwdef
  have hvi : Integrable v := lowBlock_integrable hU c
  obtain ⟨D, hD⟩ := lowBlock_bound (LT := LT) hU c
  have hwi : Integrable w := hG0i.sub hvi
  have hCw : ∀ x, ‖w x‖ ≤ CG + D := fun x =>
    (norm_sub_le _ _).trans (add_le_add (hCG x) (hD x))
  have hwsupp : Function.support w ⊆ Icc 0 LT := fun x hx => by
    by_contra hxn
    have h1 : G0 x = 0 := by
      by_contra h; exact hxn (hG0s h)
    have h2 : v x = 0 := by
      simp only [hv, lowBlock, Set.indicator_of_notMem hxn]
    exact hx (by simp only [hwdef, h1, h2, sub_zero])
  have hwmom : MomentZero w := by
    have hvmom := lowBlock_momentZero hU hUmom c
    have hwt : ∀ E : ℝ → ℂ, Continuous E →
        (∫ u, E u * w u) = (∫ u, E u * G0 u) - ∫ u, E u * v u := fun E hE => by
      have h1 : Integrable fun u => E u * G0 u :=
        (hE.mul hG0c).integrable_of_hasCompactSupport hG0cs.mul_left
      have h2 : Integrable fun u => E u * v u :=
        integrable_weight_indicator (lowBlock_continuous_sum hU c) hE
      rw [← integral_sub h1 h2]
      congr 1; funext u; simp only [hwdef]; ring
    refine ⟨?_, ?_⟩
    · rw [hwt (fun u => (Real.exp (-u / 2) : ℂ)) (by fun_prop), hG0mom.1, hvmom.1, sub_zero]
    · rw [hwt (fun u => (Real.exp (u / 2) : ℂ)) (by fun_prop), hG0mom.2, hvmom.2, sub_zero]
  have hworth : ∀ i, ∫ x in Icc 0 LT, w x * conj (U i x) = 0 := fun i => by
    rw [← hc i]
    refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
    simp only [hwdef, hv, lowBlock, Set.indicator_of_mem hx]
  have hEw : Integrable (energy w) := by
    refine (((hEG0.const_mul 2).add ((hEU c).const_mul 2))).mono'
      (energy_continuous hwi).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    show ‖energy w t‖ ≤ 2 * energy G0 t + 2 * energy v t
    rw [Real.norm_of_nonneg (show 0 ≤ energy w t from Complex.normSq_nonneg _)]
    exact energy_sub_le hG0i hvi t
  have hSw : Integrable fun t => ScertM M t * energy w t := by
    refine ((hSG0.norm.const_mul 2).add ((hSU c).norm.const_mul 2)).mono'
      ((scertM_measurable M).aestronglyMeasurable.mul (energy_continuous hwi).aestronglyMeasurable)
      (Eventually.of_forall fun t => ?_)
    have h0G : 0 ≤ energy G0 t := Complex.normSq_nonneg _
    have h0v : 0 ≤ energy v t := Complex.normSq_nonneg _
    have h0w : 0 ≤ energy w t := Complex.normSq_nonneg _
    show ‖ScertM M t * energy w t‖ ≤
      2 * ‖ScertM M t * energy G0 t‖ + 2 * ‖ScertM M t * energy v t‖
    rw [norm_mul, norm_mul, norm_mul, Real.norm_of_nonneg h0G, Real.norm_of_nonneg h0v,
      Real.norm_of_nonneg h0w]
    have := mul_le_mul_of_nonneg_left (energy_sub_le hG0i hvi t) (norm_nonneg (ScertM M t))
    linarith
  -- the three bounds
  have hcomp := complement_bound_with_moments M L m s hsm B hsB hs0 H hHc hHi hFH hHs d j hcert hwi hCw hLT0
    hwsupp (by linarith) hwmom hEw hSw U hU hworth cf hR hT
  have hX := hcross c w ⟨hwi, ⟨_, hCw⟩, hwsupp, hwmom, hworth, hEw⟩
  have hl := hlow c
  have hdec : (fun u => v u + w u) = G0 := by
    funext u; simp only [hwdef]; ring
  rw [zero_quadratic_eq_energy g hm r a hw M (by linarith)]
  have e : (∫ t, ScertM M t * energy (Gm g) t) =
      ∫ t, ScertM M t * energy (fun u => v u + w u) t := by
    rw [hdec]
    congr 1; funext t; rw [hEG]
  rw [e, quad_add (ScertM M) (scertM_measurable M).aestronglyMeasurable hvi hwi (hSU c) hSw]
  exact mul_nonneg (by positivity)
    (feshbach_combine hcpos (integral_nonneg fun t => Complex.normSq_nonneg _) (hK c) hcomp hX hl)

/-- The original 139-dimensional low family enlarged to 141 for trace only. -/
def actualTraceBasis (U : Fin 139 → ℝ → ℂ) : Fin 141 → ℝ → ℂ :=
  augment U

theorem actualTraceBasis_continuous {U : Fin 139 → ℝ → ℂ}
    (hU : ∀ i, Continuous (U i)) :
    ∀ i, Continuous (actualTraceBasis U i) :=
  augment_continuous hU

end AEGIS.CvSMomentWindowBridgeV1

#print axioms AEGIS.CvSMomentWindowBridgeV1.admissible_augmented_orthogonal
#print axioms AEGIS.CvSMomentWindowBridgeV1.window_nonneg_of_augmented_trace
#print axioms AEGIS.CvSMomentWindowBridgeV1.actualTraceBasis_continuous
#print axioms AEGIS.CvSMomentWindowBridgeV1.window_of_certificate_augmented_trace
