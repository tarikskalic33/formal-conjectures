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
import CvSTraceV1
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases

/-!+# Moment functions in the CvS trace trial space

The trace computation in `feshbach_arb_v2/complement_trace_arb.py` includes
`exp(-x/2)` and `exp(x/2)` in addition to the finite moment-zero block.
Every admissible complement is already orthogonal to these two functions.
Adding them to the trace trial space therefore leaves the finite block and
its cross-term certificate unchanged. This does not supply a trace enclosure
or the pointwise Krein certificate.
-/

open MeasureTheory FourierTransform Complex Set
open scoped ComplexConjugate

noncomputable section

namespace AEGIS.CvSMomentTraceV1

open AEGIS.CvSRoughV1 AEGIS.CvSTraceV1 AEGIS.CvSKreinRoughV1
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3

/-- The two real exponential moment functions, with the original signs. -/
def momentFunction (i : Fin 2) (x : ℝ) : ℂ :=
  (Real.exp ((if i = 0 then -x else x) / 2) : ℂ)

/-- The trace trial space may include both moment directions. -/
def augment {p : ℕ} (U : Fin p → ℝ → ℂ) : Fin (p + 2) → ℝ → ℂ :=
  Fin.append U momentFunction

theorem momentFunction_continuous (i : Fin 2) : Continuous (momentFunction i) := by
  fin_cases i
  · change Continuous (fun x : ℝ => (Real.exp (-x / 2) : ℂ))
    fun_prop
  · change Continuous (fun x : ℝ => (Real.exp (x / 2) : ℂ))
    fun_prop

theorem augment_continuous {p : ℕ} {U : Fin p → ℝ → ℂ}
    (hU : ∀ i, Continuous (U i)) : ∀ i, Continuous (augment U i) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [augment, Fin.append_left] using hU j
  · simpa only [augment, Fin.append_right] using momentFunction_continuous j

/-- The two global moments give the required conjugated interval pairings. -/
theorem moment_orthogonal {w : ℝ → ℂ} {lo hi : ℝ}
    (hsupp : Function.support w ⊆ Icc lo hi) (hmom : MomentZero w) (i : Fin 2) :
    (∫ x in Icc lo hi, w x * conj (momentFunction i x)) = 0 := by
  have hzero : ∀ x, x ∉ Icc lo hi → w x * conj (momentFunction i x) = 0 := by
    intro x hx
    have hw : w x = 0 := by
      by_contra hn
      exact hx (hsupp hn)
    rw [hw, zero_mul]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  fin_cases i
  · change (∫ x : ℝ, w x * conj ((Real.exp (-x / 2) : ℂ))) = 0
    simpa only [Complex.conj_ofReal, mul_comm] using hmom.1
  · change (∫ x : ℝ, w x * conj ((Real.exp (x / 2) : ℂ))) = 0
    simpa only [Complex.conj_ofReal, mul_comm] using hmom.2

theorem augment_orthogonal {w : ℝ → ℂ} {lo hi : ℝ}
    (hsupp : Function.support w ⊆ Icc lo hi) (hmom : MomentZero w)
    {p : ℕ} {U : Fin p → ℝ → ℂ}
    (horth : ∀ i, (∫ x in Icc lo hi, w x * conj (U i x)) = 0) :
    ∀ i, (∫ x in Icc lo hi, w x * conj (augment U i x)) = 0 := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [augment, Fin.append_left] using horth j
  · simpa only [augment, Fin.append_right] using moment_orthogonal hsupp hmom j

/-- Cauchy--Schwarz with both moment functions available at no new orthogonality cost. -/
theorem energy_le_augmented_dist {w : ℝ → ℂ} {lo hi C : ℝ}
    (hsupp : Function.support w ⊆ Icc lo hi) (hwm : AEStronglyMeasurable w)
    (hC : ∀ x, ‖w x‖ ≤ C) (hmom : MomentZero w)
    {p : ℕ} (U : Fin p → ℝ → ℂ) (hU : ∀ i, Continuous (U i))
    (horth : ∀ i, (∫ x in Icc lo hi, w x * conj (U i x)) = 0)
    (c : Fin (p + 2) → ℂ) (t : ℝ) :
    energy w t ≤ (∫ x in Icc lo hi, ‖w x‖ ^ 2) *
      trialDist lo hi (augment U) (fun _ => c) t :=
  energy_le_dist hsupp hwm hC (augment U) (augment_continuous hU)
    (augment_orthogonal hsupp hmom horth) c t

/-- The old trace-to-energy theorem consumes the augmented trial distance directly. -/
theorem slack_le_augmented_trace {w : ℝ → ℂ} {lo hi C : ℝ} (hw : Integrable w)
    (hsupp : Function.support w ⊆ Icc lo hi) (hC : ∀ x, ‖w x‖ ≤ C)
    (hmom : MomentZero w) {p : ℕ} (U : Fin p → ℝ → ℂ)
    (hU : ∀ i, Continuous (U i))
    (horth : ∀ i, (∫ x in Icc lo hi, w x * conj (U i x)) = 0)
    (s : ℝ → ℝ) (hs0 : ∀ t, 0 ≤ s t) (hsm : Measurable s)
    (B : ℝ) (hsB : ∀ t, |s t| ≤ B) (cf : ℝ → Fin (p + 2) → ℂ)
    (hR : Integrable fun t => s t * trialDist lo hi (augment U) cf t)
    {T : ℝ} (hT : ∫ t, s t * trialDist lo hi (augment U) cf t ≤ T)
    (hE : Integrable (energy w)) :
    ∫ t, s t * energy w t ≤ T / (2 * Real.pi) * ∫ t, energy w t :=
  slack_le_trace hw hsupp hC (augment U) (augment_continuous hU)
    (augment_orthogonal hsupp hmom horth) s hs0 hsm B hsB cf hR hT hE

/-- The actual Krein complement bound with the original two moment directions restored. -/
theorem complement_bound_with_moments (M : ℕ) (L m : ℝ) (s : ℝ → ℝ)
    (hsm : Measurable s) (B : ℝ) (hsB : ∀ t, |s t| ≤ B) (hs0 : ∀ t, 0 ≤ s t)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i))
    (hHi : ∀ i, Integrable (H i)) (hFH : ∀ i, Integrable (𝓕 (H i)))
    (hHs : ∀ i u, |u| < L → H i u = 0) {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (ScertM M t - m) +
      (∑ i, 𝓕 (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re + Wt t * s t)
    {w : ℝ → ℂ} (hw : Integrable w) {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C)
    {lo hi : ℝ} (hlh : lo ≤ hi) (hsupp : Function.support w ⊆ Icc lo hi)
    (hlen : hi - lo < L) (hmom : MomentZero w) (hE : Integrable (energy w))
    (hSE : Integrable fun t => ScertM M t * energy w t)
    {p : ℕ} (U : Fin p → ℝ → ℂ) (hU : ∀ i, Continuous (U i))
    (horth : ∀ i, (∫ x in Icc lo hi, w x * conj (U i x)) = 0)
    (cf : ℝ → Fin (p + 2) → ℂ)
    (hR : Integrable fun t => s t * trialDist lo hi (augment U) cf t)
    {T : ℝ} (hT : ∫ t, s t * trialDist lo hi (augment U) cf t ≤ T) :
    (m - T / (2 * Real.pi)) * ∫ t, energy w t ≤ ∫ t, ScertM M t * energy w t :=
  complement_bound M L m s hsm B hsB hs0 H hHc hHi hFH hHs d j hcert
    hw hC hlh hsupp hlen hmom hE hSE (augment U) (augment_continuous hU)
    (augment_orthogonal hsupp hmom horth) cf hR hT

end AEGIS.CvSMomentTraceV1

#print axioms AEGIS.CvSMomentTraceV1.momentFunction_continuous
#print axioms AEGIS.CvSMomentTraceV1.augment_continuous
#print axioms AEGIS.CvSMomentTraceV1.moment_orthogonal
#print axioms AEGIS.CvSMomentTraceV1.augment_orthogonal
#print axioms AEGIS.CvSMomentTraceV1.energy_le_augmented_dist
#print axioms AEGIS.CvSMomentTraceV1.slack_le_augmented_trace
#check @AEGIS.CvSMomentTraceV1.complement_bound_with_moments
#print axioms AEGIS.CvSMomentTraceV1.complement_bound_with_moments
