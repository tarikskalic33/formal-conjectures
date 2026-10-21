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
/- Source candidate: actual finite row contracts composed with the existing uniform Gram-tail window.
Not a kernel result until replayed. The Krein/trace/scalar hypotheses remain explicit. -/
import CvSActualRowConsumerV1
import CvSTauFarL12V1
import CvSKreinScalarUniformV1
open MeasureTheory Complex
open scoped BigOperators ComplexConjugate
namespace AEGIS.CvSActualGramWindowV1
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open AEGIS.CvSGramTailV1 AEGIS.CvSRowTailV1 AEGIS.CvSCrossCertV1
open AEGIS.CvSLowBlockMatrixV1 AEGIS.CvSMomentBasisV1 AEGIS.CvSTraceV1
open AEGIS.CvSWindowCertV1 AEGIS.CvSFeshbachWindowV1
open AEGIS.CvSSchurClosureFromBoundsV1 AEGIS.CvSProjectedPackedCertificateL12V1
open AEGIS.CvSActualRowConsumerV1
open AEGIS.WeilCriticalLineKreinFormV1 AEGIS.RHDyadicDiagonalV13
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3

/-- The already-proved tail majorant is nonnegative: take outer cutoff zero. -/
theorem gramUp_nonneg {F : Finset ℤ} {R NP : ℕ}
    (hF : ∀ n ∈ F, |(n : ℝ)| ≤ R) (hRNP : R < NP) (v : ℤ → ℂ) :
    0 ≤ gform F v (gramUp NP) := by
  have hz : (Finset.Icc (-(0 : ℤ)) 0).filter (fun x => NP < x.natAbs) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hx, habs⟩
    have hx0 : x = 0 := by
      have hi := Finset.mem_Icc.mp hx
      omega
    subst x
    norm_num at habs
  have h := gram_tail_le hF hRNP v 0
  simpa only [Nat.cast_zero, hz, Finset.sum_empty] using h

/-- Positivity of the actual Gram-tail majorant at every admissible cutoff. -/
theorem gramTail_nonneg (M : ℕ) (L : ℝ) {F : Finset ℤ} {R NP : ℕ}
    (hF : ∀ n ∈ F, |(n : ℝ)| ≤ R) (hRNP : R < NP)
    (v : ℤ → ℂ) (T : ℝ) {epsilon : ℝ} (he : 0 < epsilon) :
    0 ≤ gramTail M L F v T epsilon NP := by
  have h1 := gramUp_nonneg hF hRNP (fun n => v n * (tau M L n : ℂ))
  have h2 := gramUp_nonneg hF hRNP v
  unfold gramTail
  positivity

theorem support_bound : ∀ n ∈ lowFreq supports, |(n : ℝ)| ≤ (70 : ℕ) := by
  intro n hn
  rw [AEGIS.CvSProjectedTransportL12V1.lowFreq_mem_iff] at hn
  have hz : |n| ≤ (70 : ℤ) := abs_le.mpr hn
  exact_mod_cast hz

/-- Nonnegativity comes from the original residual rows and actual Gram tail. -/
theorem Brow_nonneg (M : ℕ) (c : Fin 139 → ℂ) : 0 ≤ Brow M c := by
  have ht := gramTail_nonneg M (6/5) support_bound (by decide : 70 < 150)
    (lowCoeff (6/5) supports weights c) 13 (by norm_num : (0 : ℝ) < 1)
  have hf := hfin M c
  have hr : 0 ≤ ∑ m ∈ Finset.Icc (-150 : ℤ) 150,
      ‖crossRow M (6/5) (lowFreq supports) (lowCoeff (6/5) supports weights c) m -
        ∑ j, lam c j * atomRow (6/5) supports weights j m‖^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  exact (add_nonneg hr ht).trans hf

/-- This source coercivity route needs no replay of the historical bigCheck. -/
theorem actual_Q_nonneg (M : ℕ) (hM : 3 ≤ M) (c : Fin 139 → ℂ) :
    0 ≤ Q_CvS M (6/5) atomCenter c := by
  have h := (Brow_nonneg M c).trans (hB M hM c)
  linarith

theorem gap_positive (m T : ℝ)
    (hk : 40 ≤ (2 * Real.pi)^2 * (6/5 : ℝ) * (m - T/(2*Real.pi))) :
    0 < m - T/(2*Real.pi) := by
  have hc : 0 ≤ (2 * Real.pi)^2 * (6/5 : ℝ) := by positivity
  by_contra h
  have hn := mul_nonpos_of_nonneg_of_nonpos hc (le_of_not_gt h)
  linarith

/-- The exact relative-budget algebra applied to the newly certified actual form. -/
theorem actual_hlow (M : ℕ) (hM : 3 ≤ M) (m T : ℝ)
    (hk : 40 ≤ (2 * Real.pi)^2 * (6/5 : ℝ) * (m - T/(2*Real.pi))) :
    ∀ c, Brow M c / (2*Real.pi*(6/5 : ℝ)) / (m - T/(2*Real.pi)) ≤
      2*Real.pi*Q_CvS M (6/5) atomCenter c := by
  intro c
  have hg := gap_positive m T hk
  have hd : 0 < 2*Real.pi*(6/5 : ℝ) := by positivity
  rw [div_div, div_le_iff₀ (mul_pos hd hg)]
  calc
    _ ≤ 40 * Q_CvS M (6/5) atomCenter c := hB M hM c
    _ ≤ ((2*Real.pi)^2*(6/5 : ℝ)*(m-T/(2*Real.pi))) * Q_CvS M (6/5) atomCenter c :=
      mul_le_mul_of_nonneg_right hk (actual_Q_nonneg M hM c)
    _ = _ := by ring

/-- The existing actual zero-side window, with the finite rows and relative budget discharged. -/
theorem window_of_actual_rows (M : ℕ) (hM : 3 ≤ M) (L m : ℝ) (hLTL : (6/5 : ℝ) < L)
    (s : ℝ → ℝ) (hsm : Measurable s) (B : ℝ) (hsB : ∀ t, |s t| ≤ B) (hs0 : ∀ t, 0 ≤ s t)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (FourierTransform.fourier (H i)))
    (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (ScertM M t - m) +
      (∑ i, FourierTransform.fourier (H i) (t/(2*Real.pi))).re +
      ∑ l, 2*(d l*((I*(t : ℂ))^j l*Complex.exp (↑(t*L)*I))).re + Wt t*s t)
    (cf : ℝ → Fin 139 → ℂ)
    (hR : Integrable fun t =>
      s t * trialDist 0 (6/5) (fun i => momentAtom (6/5) (atomCenter i)) cf t)
    {T : ℝ}
    (hT : ∫ t, s t * trialDist 0 (6/5) (fun i => momentAtom (6/5) (atomCenter i)) cf t ≤ T)
    (hk : 40 ≤ (2*Real.pi)^2*(6/5 : ℝ)*(m-T/(2*Real.pi)))
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (r a : ℝ)
    (hw : HalfWidthAt g r a) (h2r : 2*r ≤ 6/5) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  have hlog : (6/5 : ℝ) < Real.log ((M+1 : ℕ) : ℝ) := by
    have h4 : (4 : ℝ) ≤ ((M+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 4 ≤ M+1)
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 4) h4
    have he : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
      push_cast
      ring
    linarith [Real.log_two_gt_d9]
  have hi : ∀ i : Fin 139, |atomCenter i| + 1 ≤ (70 : ℤ) := by
    intro i
    have h := i.isLt
    simp only [atomCenter]
    have : |(i.val : ℤ)-69| ≤ 69 := abs_le.mpr ⟨by omega, by omega⟩
    omega
  exact window_of_certificate_gram M L (6/5) m (by norm_num) hLTL hlog
    s hsm B hsB hs0 H hHc hHi hFH hHs d j hcert atomCenter cf hR hT
    (gap_positive m T hk) 70 150 hi (by decide)
    (fun x hx => AEGIS.CvSTauFarL12V1.tau_abs_le_far hM
      (by rw [← Int.natCast_natAbs]; omega)) (by norm_num : (0 : ℝ) < 1)
    lam (Brow M) (hfin M) (actual_hlow M hM m T hk) g hm r a hw h2r
/-- A coarser trace bound suffices, with an exact positive scalar reserve. -/
theorem window_of_trace_le_six (M : ℕ) (hM : 3 ≤ M) (L m : ℝ) (hLTL : (6/5 : ℝ) < L)
    (s : ℝ → ℝ) (hsm : Measurable s) (B : ℝ) (hsB : ∀ t, |s t| ≤ B) (hs0 : ∀ t, 0 ≤ s t)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (FourierTransform.fourier (H i)))
    (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (ScertM M t - m) +
      (∑ i, FourierTransform.fourier (H i) (t/(2*Real.pi))).re +
      ∑ l, 2*(d l*((I*(t : ℂ))^j l*Complex.exp (↑(t*L)*I))).re + Wt t*s t)
    (cf : ℝ → Fin 139 → ℂ)
    (hR : Integrable fun t =>
      s t * trialDist 0 (6/5) (fun i => momentAtom (6/5) (atomCenter i)) cf t)
    (hT : ∫ t, s t * trialDist 0 (6/5) (fun i => momentAtom (6/5) (atomCenter i)) cf t ≤ 6)
    (hm0 : (31/16 : ℝ) ≤ m)
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (r a : ℝ)
    (hw : HalfWidthAt g r a) (h2r : 2*r ≤ 6/5) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  exact window_of_actual_rows M hM L m hLTL s hsm B hsB hs0 H hHc hHi hFH hHs
    d j hcert cf hR hT (AEGIS.CvSKreinScalarUniformV1.schur_budget hm0 (le_refl 6))
    g hm r a hw h2r

end AEGIS.CvSActualGramWindowV1
#print axioms AEGIS.CvSActualGramWindowV1.gramUp_nonneg
#print axioms AEGIS.CvSActualGramWindowV1.gramTail_nonneg
#print axioms AEGIS.CvSActualGramWindowV1.Brow_nonneg
#print axioms AEGIS.CvSActualGramWindowV1.actual_Q_nonneg
#print axioms AEGIS.CvSActualGramWindowV1.actual_hlow
#check @AEGIS.CvSActualGramWindowV1.window_of_actual_rows
#print axioms AEGIS.CvSActualGramWindowV1.window_of_actual_rows

#check @AEGIS.CvSActualGramWindowV1.window_of_trace_le_six
#print axioms AEGIS.CvSActualGramWindowV1.window_of_trace_le_six
