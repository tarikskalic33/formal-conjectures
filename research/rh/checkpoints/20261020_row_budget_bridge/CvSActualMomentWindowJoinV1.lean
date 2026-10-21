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

import CvSMomentWindowBridgeV1
import CvSActualGramWindowV1

/-!
# Actual CvS rows with the two added exponential trace moments
This module transports the already-proved 139-dimensional Gram/cross/Schur
calculation unchanged. Only complementary trace-distance certificates use the
141-dimensional augmented family. Existing proofs were read at the exact
base HEAD and copied with their mathematical bodies unchanged except for the
trace-family arguments and calls to the preceding augmented-wrapper lemmas.
The Krein pointwise inequality and actual augmented trace bound are explicit
assumptions. This is not RH.
-/
open MeasureTheory FourierTransform Complex Set Filter
open scoped ComplexConjugate ContDiff InnerProductSpace
noncomputable section
namespace AEGIS.CvSActualMomentWindowJoinV1
open AEGIS.CvSMomentWindowBridgeV1 AEGIS.CvSMomentTraceV1
open AEGIS.CvSActualGramWindowV1 AEGIS.CvSKreinScalarUniformV1
open AEGIS.CvSWindowCertV1 AEGIS.CvSLowBlockDecayV1 AEGIS.CvSMomentBasisV1
open AEGIS.CvSLowBlockMatrixV1 AEGIS.CvSCrossCertV1 AEGIS.CvSGramTailV1
open AEGIS.CvSFeshbachWindowV1 AEGIS.CvSRowTailV1 AEGIS.CvSWindowL12V1
open AEGIS.CvSRoughV1 AEGIS.CvSKreinRoughV1 AEGIS.CvSPlancherelRoughV1
open AEGIS.CvSTraceV1 AEGIS.CvSCrossBoundV1 AEGIS.CvSRingBridgeV1
open AEGIS.CvSFeshbachWindowV1 AEGIS.CvSDigammaSeriesV1
open AEGIS.CvSLowBlockMatrixV1 AEGIS.CvSWindowCertV1
open AEGIS.WeilCriticalLineKreinFormV1 AEGIS.RHDyadicDiagonalV13
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

/-- Original source-bound theorem: CvSLowBlockDecayV1.window_of_certificate_C1; only augmented trace interface. -/
theorem window_of_certificate_C1_moment (M : ℕ) (L LT m : ℝ) (hLT0 : 0 ≤ LT) (hLTL : LT < L)
    (hLTM : LT < Real.log ((M + 1 : ℕ) : ℝ))
    (s : ℝ → ℝ) (hsm : Measurable s) (B : ℝ) (hsB : ∀ t, |s t| ≤ B) (hs0 : ∀ t, 0 ≤ s t)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (𝓕 (H i))) (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (ScertM M t - m) + (∑ i, 𝓕 (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re + Wt t * s t)
    {p : ℕ} (U : Fin p → ℝ → ℂ) (hU : ∀ i, ContDiff ℝ 1 (U i))
    (hUmom : ∀ i, MomentZero (Set.indicator (Icc 0 LT) (U i)))
    (cf : ℝ → Fin (p + 2) → ℂ) (hR : Integrable fun t => s t * trialDist 0 LT (augment U) cf t)
    {T : ℝ} (hT : ∫ t, s t * trialDist 0 LT (augment U) cf t ≤ T) (hcpos : 0 < m - T / (2 * Real.pi))
    (K : (Fin p → ℂ) → ℝ) (hK : ∀ c, 0 ≤ K c)
    (hcross : ∀ c w, Admissible LT U w →
      (∫ t, ScertM M t * cross (lowBlock LT U c) w t) ^ 2 ≤ K c * ∫ t, energy w t)
    (hlow : ∀ c, K c / (m - T / (2 * Real.pi)) ≤ ∫ t, ScertM M t * energy (lowBlock LT U c) t)
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (r a : ℝ)
    (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ LT) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re :=
  window_of_certificate_augmented_trace M L LT m hLT0 hLTL hLTM s hsm B hsB hs0 H hHc hHi hFH hHs d j hcert U
    (fun i => (hU i).continuous) hUmom cf hR hT hcpos
    (fun c => lowBlock_energy_integrable hLT0 hU c)
    (fun c => lowBlock_scertM_integrable M hLT0 hU c) K hK hcross hlow g hm r a hw h2r

/-- Original source-bound theorem: CvSMomentBasisV1.window_of_certificate_basis; only augmented trace interface. -/
theorem window_of_certificate_basis_moment (M : ℕ) (L LT m : ℝ) (hLT0 : 0 < LT) (hLTL : LT < L)
    (hLTM : LT < Real.log ((M + 1 : ℕ) : ℝ))
    (s : ℝ → ℝ) (hsm : Measurable s) (B : ℝ) (hsB : ∀ t, |s t| ≤ B) (hs0 : ∀ t, 0 ≤ s t)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (FourierTransform.fourier (H i)))
    (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (ScertM M t - m) +
      (∑ i, FourierTransform.fourier (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re + Wt t * s t)
    {p : ℕ} (ι : Fin p → ℤ)
    (cf : ℝ → Fin (p + 2) → ℂ)
    (hR : Integrable fun t => s t * trialDist 0 LT (augment (fun i => momentAtom LT (ι i))) cf t)
    {T : ℝ} (hT : ∫ t, s t * trialDist 0 LT (augment (fun i => momentAtom LT (ι i))) cf t ≤ T)
    (hcpos : 0 < m - T / (2 * Real.pi))
    (K : (Fin p → ℂ) → ℝ) (hK : ∀ c, 0 ≤ K c)
    (hcross : ∀ c w, Admissible LT (fun i => momentAtom LT (ι i)) w →
      (∫ t, ScertM M t * cross (lowBlock LT (fun i => momentAtom LT (ι i)) c) w t) ^ 2 ≤
        K c * ∫ t, energy w t)
    (hlow : ∀ c, K c / (m - T / (2 * Real.pi)) ≤
      ∫ t, ScertM M t * energy (lowBlock LT (fun i => momentAtom LT (ι i)) c) t)
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (r a : ℝ)
    (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ LT) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re :=
  window_of_certificate_C1_moment M L LT m hLT0.le hLTL hLTM s hsm B hsB hs0 H hHc hHi hFH hHs d j hcert
    (fun i => momentAtom LT (ι i)) (fun i => (basisFun_contDiff _ _ _).of_le (by norm_cast))
    (fun i => momentAtom_momentZero hLT0 (ι i)) cf hR hT hcpos K hK hcross hlow g hm r a hw h2r

/-- Original source-bound theorem: CvSLowBlockMatrixV1.window_of_certificate_matrix; only augmented trace interface. -/
theorem window_of_certificate_matrix_moment (M : ℕ) (L LT m : ℝ) (hLT0 : 0 < LT) (hLTL : LT < L)
    (hLTM : LT < Real.log ((M + 1 : ℕ) : ℝ))
    (s : ℝ → ℝ) (hsm : Measurable s) (B : ℝ) (hsB : ∀ t, |s t| ≤ B) (hs0 : ∀ t, 0 ≤ s t)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (FourierTransform.fourier (H i)))
    (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (ScertM M t - m) +
      (∑ i, FourierTransform.fourier (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re + Wt t * s t)
    {p : ℕ} (ι : Fin p → ℤ)
    (cf : ℝ → Fin (p + 2) → ℂ)
    (hR : Integrable fun t => s t * trialDist 0 LT (augment (fun i => momentAtom LT (ι i))) cf t)
    {T : ℝ} (hT : ∫ t, s t * trialDist 0 LT (augment (fun i => momentAtom LT (ι i))) cf t ≤ T)
    (hcpos : 0 < m - T / (2 * Real.pi))
    (K : (Fin p → ℂ) → ℝ) (hK : ∀ c, 0 ≤ K c)
    (hcross : ∀ c w, Admissible LT (fun i => momentAtom LT (ι i)) w →
      (∫ t, ScertM M t * cross (lowBlock LT (fun i => momentAtom LT (ι i)) c) w t) ^ 2 ≤
        K c * ∫ t, energy w t)
    (hlow : ∀ c, K c / (m - T / (2 * Real.pi)) ≤ 2 * Real.pi *
      (∑ a ∈ lowFreq (fun i => sinSqSupport (ι i)), ∑ b ∈ lowFreq (fun i => sinSqSupport (ι i)),
        lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c a *
          conj (lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c b) *
            (cvsEntry M LT a b : ℂ)).re)
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (r a : ℝ)
    (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ LT) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re :=
  window_of_certificate_basis_moment M L LT m hLT0 hLTL hLTM s hsm B hsB hs0 H hHc hHi hFH hHs d j hcert
    ι cf hR hT hcpos K hK hcross
    (fun c => (lowBlock_quad_re M hLT0 (fun i => sinSqSupport (ι i))
      (fun i => sinSqWeight (ι i)) c).symm ▸ hlow c) g hm r a hw h2r

/-- Original source-bound theorem: CvSCrossCertV1.window_of_certificate_rows; only augmented trace interface. -/
theorem window_of_certificate_rows_moment (M : ℕ) (L LT m : ℝ) (hLT0 : 0 < LT) (hLTL : LT < L)
    (hLTM : LT < Real.log ((M + 1 : ℕ) : ℝ))
    (s : ℝ → ℝ) (hsm : Measurable s) (B : ℝ) (hsB : ∀ t, |s t| ≤ B) (hs0 : ∀ t, 0 ≤ s t)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (FourierTransform.fourier (H i)))
    (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (ScertM M t - m) +
      (∑ i, FourierTransform.fourier (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re + Wt t * s t)
    {p : ℕ} (ι : Fin p → ℤ)
    (cf : ℝ → Fin (p + 2) → ℂ)
    (hR : Integrable fun t => s t * trialDist 0 LT (augment (fun i => momentAtom LT (ι i))) cf t)
    {T : ℝ} (hT : ∫ t, s t * trialDist 0 LT (augment (fun i => momentAtom LT (ι i))) cf t ≤ T)
    (hcpos : 0 < m - T / (2 * Real.pi))
    (lam : (Fin p → ℂ) → Fin p → ℂ) (Brow : (Fin p → ℂ) → ℝ)
    (hrows : ∀ c (N : ℕ), ∑ a ∈ Finset.Icc (-(N : ℤ)) N,
      ‖crossRow M LT (lowFreq fun i => sinSqSupport (ι i))
          (lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c) a -
        ∑ i, lam c i *
          atomRow LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) i a‖ ^ 2 ≤
          Brow c)
    (hlow : ∀ c, Brow c / (2 * Real.pi * LT) / (m - T / (2 * Real.pi)) ≤ 2 * Real.pi *
      (∑ a ∈ lowFreq (fun i => sinSqSupport (ι i)), ∑ b ∈ lowFreq (fun i => sinSqSupport (ι i)),
        lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c a *
          conj (lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c b) *
            (cvsEntry M LT a b : ℂ)).re)
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (r a : ℝ)
    (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ LT) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  have hBrow : ∀ c, 0 ≤ Brow c := fun c =>
    (Finset.sum_nonneg fun _ _ => sq_nonneg _).trans (hrows c 0)
  refine window_of_certificate_matrix_moment M L LT m hLT0 hLTL hLTM s hsm B hsB hs0 H hHc hHi hFH hHs
    d j hcert ι cf hR hT hcpos (fun c => Brow c / (2 * Real.pi * LT))
    (fun c => div_nonneg (hBrow c) (by positivity)) (fun c w hw => ?_) hlow g hm r a hw h2r
  exact cross_sq_le_of_rows M hLT0 (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c
    (lam c) (Brow c) (hrows c) hw

/-- Original source-bound theorem: CvSGramTailV1.window_of_certificate_gram; only augmented trace interface. -/
theorem window_of_certificate_gram_moment (M : ℕ) (L LT m : ℝ) (hLT0 : 0 < LT) (hLTL : LT < L)
    (hLTM : LT < Real.log ((M + 1 : ℕ) : ℝ))
    (s : ℝ → ℝ) (hsm : Measurable s) (B : ℝ) (hsB : ∀ t, |s t| ≤ B) (hs0 : ∀ t, 0 ≤ s t)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (FourierTransform.fourier (H i)))
    (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (ScertM M t - m) +
      (∑ i, FourierTransform.fourier (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re + Wt t * s t)
    {p : ℕ} (ι : Fin p → ℤ)
    (cf : ℝ → Fin (p + 2) → ℂ)
    (hR : Integrable fun t => s t * trialDist 0 LT (augment (fun i => momentAtom LT (ι i))) cf t)
    {T : ℝ} (hT : ∫ t, s t * trialDist 0 LT (augment (fun i => momentAtom LT (ι i))) cf t ≤ T)
    (hcpos : 0 < m - T / (2 * Real.pi))
    (R NP : ℕ) (hRι : ∀ i, |ι i| + 1 ≤ (R : ℤ)) (hRNP : R < NP)
    {Tτ : ℝ} (hTτ : ∀ x : ℤ, NP < x.natAbs → |tau M LT x| ≤ Tτ) {ε : ℝ} (hε : 0 < ε)
    (lam : (Fin p → ℂ) → Fin p → ℂ) (Brow : (Fin p → ℂ) → ℝ)
    (hfin : ∀ c, (∑ a ∈ Finset.Icc (-(NP : ℤ)) NP,
      ‖crossRow M LT (lowFreq fun i => sinSqSupport (ι i))
          (lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c) a -
        ∑ i, lam c i *
          atomRow LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) i a‖ ^ 2) +
      gramTail M LT (lowFreq fun i => sinSqSupport (ι i))
        (lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c) Tτ ε NP ≤
        Brow c)
    (hlow : ∀ c, Brow c / (2 * Real.pi * LT) / (m - T / (2 * Real.pi)) ≤ 2 * Real.pi *
      (∑ a ∈ lowFreq (fun i => sinSqSupport (ι i)), ∑ b ∈ lowFreq (fun i => sinSqSupport (ι i)),
        lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c a *
          conj (lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c b) *
            (cvsEntry M LT a b : ℂ)).re)
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (r a : ℝ)
    (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ LT) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  set S : Fin p → Finset ℤ := fun i => sinSqSupport (ι i)
  set β : Fin p → ℤ → ℂ := fun i => sinSqWeight (ι i)
  have hF : ∀ n ∈ lowFreq S, |(n : ℝ)| ≤ R := by
    intro n hn
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hn
    have hn' : n = ι i - 1 ∨ n = ι i ∨ n = ι i + 1 := by
      simpa [S, sinSqSupport] using hi
    have h1 := hRι i
    have h2 := neg_abs_le (ι i)
    have h3 := le_abs_self (ι i)
    have hz : |n| ≤ (R : ℤ) := by
      rw [abs_le]
      rcases hn' with h | h | h <;> subst h <;> constructor <;> linarith
    have := (Int.cast_le (R := ℝ)).mpr hz
    rwa [Int.cast_abs, Int.cast_natCast] at this
  refine window_of_certificate_rows_moment M L LT m hLT0 hLTL hLTM s hsm B hsB hs0 H hHc hHi hFH hHs
    d j hcert ι cf hR hT hcpos lam Brow (fun c N => ?_) hlow g hm r a hw h2r
  have hz : ∀ x : ℤ, NP < x.natAbs → ∑ i, lam c i * atomRow LT S β i x = 0 := by
    intro x hx
    have hxF : x ∉ lowFreq S := fun h => by
      have h1 := hF x h
      have h2 : |(x : ℝ)| = (x.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
      have h3 : (NP : ℝ) < x.natAbs := by exact_mod_cast hx
      have h4 : (R : ℝ) < NP := by exact_mod_cast hRNP
      linarith
    exact Finset.sum_eq_zero fun i _ => by rw [atomRow, lowCoeff_eq_zero LT S β _ hxF, mul_zero]
  refine (rows_split hz N).trans ?_
  refine le_trans (add_le_add le_rfl ?_) (hfin c)
  exact rows_gram_le M hLT0 hF hRNP _ hTτ hε N

/-- Original source-bound theorem: CvSActualGramWindowV1.window_of_actual_rows; only augmented trace interface. -/
theorem window_of_actual_rows_moment (M : ℕ) (hM : 3 ≤ M) (L m : ℝ) (hLTL : (6/5 : ℝ) < L)
    (s : ℝ → ℝ) (hsm : Measurable s) (B : ℝ) (hsB : ∀ t, |s t| ≤ B) (hs0 : ∀ t, 0 ≤ s t)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (FourierTransform.fourier (H i)))
    (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (ScertM M t - m) +
      (∑ i, FourierTransform.fourier (H i) (t/(2*Real.pi))).re +
      ∑ l, 2*(d l*((I*(t : ℂ))^j l*Complex.exp (↑(t*L)*I))).re + Wt t*s t)
    (cf : ℝ → Fin 141 → ℂ)
    (hR : Integrable fun t =>
      s t * trialDist 0 (6/5) (augment (fun i => momentAtom (6/5) (atomCenter i))) cf t)
    {T : ℝ}
    (hT : ∫ t, s t * trialDist 0 (6/5) (augment (fun i => momentAtom (6/5) (atomCenter i))) cf t ≤ T)
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
  exact window_of_certificate_gram_moment M L (6/5) m (by norm_num) hLTL hlog
    s hsm B hsB hs0 H hHc hHi hFH hHs d j hcert atomCenter cf hR hT
    (gap_positive m T hk) 70 150 hi (by decide)
    (fun x hx => AEGIS.CvSTauFarL12V1.tau_abs_le_far hM
      (by rw [← Int.natCast_natAbs]; omega)) (by norm_num : (0 : ℝ) < 1)
    lam (Brow M) (hfin M) (actual_hlow M hM m T hk) g hm r a hw h2r

/-- Original source-bound theorem: CvSActualGramWindowV1.window_of_trace_le_six; only augmented trace interface. -/
theorem window_of_trace_le_six_moment (M : ℕ) (hM : 3 ≤ M) (L m : ℝ) (hLTL : (6/5 : ℝ) < L)
    (s : ℝ → ℝ) (hsm : Measurable s) (B : ℝ) (hsB : ∀ t, |s t| ≤ B) (hs0 : ∀ t, 0 ≤ s t)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (FourierTransform.fourier (H i)))
    (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (ScertM M t - m) +
      (∑ i, FourierTransform.fourier (H i) (t/(2*Real.pi))).re +
      ∑ l, 2*(d l*((I*(t : ℂ))^j l*Complex.exp (↑(t*L)*I))).re + Wt t*s t)
    (cf : ℝ → Fin 141 → ℂ)
    (hR : Integrable fun t =>
      s t * trialDist 0 (6/5) (augment (fun i => momentAtom (6/5) (atomCenter i))) cf t)
    (hT : ∫ t, s t * trialDist 0 (6/5) (augment (fun i => momentAtom (6/5) (atomCenter i))) cf t ≤ 6)
    (hm0 : (31/16 : ℝ) ≤ m)
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (r a : ℝ)
    (hw : HalfWidthAt g r a) (h2r : 2*r ≤ 6/5) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  exact window_of_actual_rows_moment M hM L m hLTL s hsm B hsB hs0 H hHc hHi hFH hHs
    d j hcert cf hR hT (AEGIS.CvSKreinScalarUniformV1.schur_budget hm0 (le_refl 6))
    g hm r a hw h2r

end AEGIS.CvSActualMomentWindowJoinV1

#print axioms AEGIS.CvSActualMomentWindowJoinV1.window_of_certificate_C1_moment
#print axioms AEGIS.CvSActualMomentWindowJoinV1.window_of_certificate_basis_moment
#print axioms AEGIS.CvSActualMomentWindowJoinV1.window_of_certificate_matrix_moment
#print axioms AEGIS.CvSActualMomentWindowJoinV1.window_of_certificate_rows_moment
#print axioms AEGIS.CvSActualMomentWindowJoinV1.window_of_certificate_gram_moment
#print axioms AEGIS.CvSActualMomentWindowJoinV1.window_of_actual_rows_moment
#print axioms AEGIS.CvSActualMomentWindowJoinV1.window_of_trace_le_six_moment
