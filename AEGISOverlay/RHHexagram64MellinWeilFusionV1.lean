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

import AEGISOverlay.RHOptimizedSchurGlobalJoinV1
import AEGISOverlay.RHTranslateSpectralObstructionV1
import WeilPrimeLineIdentityV1

/-!
# AEGIS Omega: actual 64-hexagram Mellin / Weil / prime-line integration

All statements use the SAME actual `WeilCompactSmoothGV1` packet family.
There is no substituted finite spectrum, artificial Weil form or zero-sign axiom.
Finite Mellin superposition below also applies to arbitrary packet families.
The translate polynomial is a valid special case, *not* an exhaustive class
of all moment-zero source packets (see the existing Mellin-zero obstruction).

Exact-head SOURCE CANDIDATE; requires Lean 4.33.1 kernel replay on its source SHA.
-/

open Finset Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHHexagram64MellinWeilFusionV1

open AEGIS.RHGramExpansionV13
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilAutocorrelationMellinV11
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilZeroTranslationV11
open AEGIS.WeilPairedZeroEvaluationV9
open AEGIS.RHTimeSliceWeilV1
open AEGIS.RHOptimizedSchurGlobalJoinV1
open AEGIS.RHTranslateSpectralObstructionV1

/-- Complex scaling of the actual source packet commutes with Mellin. -/
private theorem mellin_scalePacket_exact
    (g : WeilCompactSmoothGV1) (z s : ℂ) :
    mellin (scalePacket z g).1 s = z * mellin g.1 s := by
  change mellin (fun x : ℝ => z * g.1 x) s = z * mellin g.1 s
  simpa [smul_eq_mul] using mellin_const_smul g.1 s z

/-- The existing compact-smooth Mellin convergence discharges both
analytic hypotheses of the Mellin-add lemma. -/
private theorem mellin_addPacket_exact
    (g h : WeilCompactSmoothGV1) (s : ℂ) :
    mellin (addPacket g h).1 s = mellin g.1 s + mellin h.1 s := by
  have hsum := hasMellin_add
    (weil_compact_smooth_mellin_convergent_all_v1 g s)
    (weil_compact_smooth_mellin_convergent_all_v1 h s)
  change mellin (fun x : ℝ => g.1 x + h.1 x) s = _
  exact hsum.2

/-- The key generality: arbitrary finite packet families, arbitrary
complex coefficients and all complex Mellin arguments. -/
theorem mellin_packetSum_exact {n : ℕ}
    (z : Fin (n + 1) → ℂ)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1) (s : ℂ) :
    mellin (packetSum z gs).1 s =
      ∑ i : Fin (n + 1), z i * mellin (gs i).1 s := by
  induction n with
  | zero => simp [packetSum, mellin_scalePacket_exact]
  | succ n ih =>
      simp only [packetSum, mellin_addPacket_exact,
        mellin_scalePacket_exact, ih, Fin.sum_univ_castSucc]

/-- UNIVERSAL Mellin/Weil/zero-side fusion for every actual moment-zero
compact Weil packet, not just translates of a fixed seed. The `gs` are
constructed by the existing smooth partition and may have arbitrary centers.
Every complex Mellin argument and every actual zeta-zero summand is retained.
No positivity of the arbitrary mixed Gram is asserted. -/
theorem every_moment_zero_packet_actual_mellin_weil_zero_fusion
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
        (center : Fin (n + 1) → ℝ),
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i)) ∧
      (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
        -(B (gs i) (gs i)).re) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (∀ s : ℂ, mellin g.1 s =
        ∑ i : Fin (n + 1), mellin (gs i).1 s) ∧
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
        (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), B (gs i) (gs j)).re ∧
      (∀ rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho =
          (analyticOrderNatAt riemannZeta rho.1 : ℂ) *
            ((∑ i : Fin (n + 1), mellin (gs i).1 rho.1) *
              conj (∑ j : Fin (n + 1),
                mellin (gs j).1 (1 - conj rho.1)))) := by
  obtain ⟨n, gs, center, hmom, hd, hw, hpacket, hgram⟩ :=
    AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram_with_support
      g hm
  have hM : ∀ s : ℂ, mellin g.1 s =
      ∑ i : Fin (n + 1), mellin (gs i).1 s := by
    intro s
    rw [hpacket, mellin_packetSum_exact]
    simp
  refine ⟨n, gs, center, hmom, hw, hd, hpacket, hM, hgram, ?_⟩
  intro rho
  rw [autocorrelation_zero_summand_factorization_v11,
    hM rho.1, hM (1 - conj rho.1)]

/-- A true von Mangoldt prime-line identity for the SAME universal
finite Mellin decomposition. This is not a sign inequality: it is an
unconditional arithmetic/Mellin dictionary for every moment-zero packet. -/
theorem every_moment_zero_packet_actual_prime_line_mellin_fusion
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (c : ℝ) (hc : 1 < c) :
    ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (1 / (2 * Real.pi) : ℝ) •
        (∫ t : ℝ,
          (-deriv riemannZeta ((c : ℂ) + t * I) /
            riemannZeta ((c : ℂ) + t * I)) *
            (∑ i : Fin (n + 1),
              mellin (gs i).1 ((c : ℂ) + t * I))) =
        ∑' m : ℕ, (ArithmeticFunction.vonMangoldt m : ℂ) *
          g.1 (m : ℝ) := by
  obtain ⟨n, gs, _center, _hmom, _hw, _hd, hpacket,
    hM, _hgram, _hzero⟩ :=
      every_moment_zero_packet_actual_mellin_weil_zero_fusion g hm
  refine ⟨n, gs, hpacket, ?_⟩
  have h := weil_compact_smooth_prime_line_identity_v1 g c hc
  simpa only [hM] using h

/-- An exact 64-term exponential polynomial of spectral log-time.
This is NOT discretization of s or truncation of the Mellin transform. -/
def hexagram64MellinMultiplier
    (p : ℝ) (ticks : Fin 64 → ℤ) (z : Fin 64 → ℂ) (s : ℂ) : ℂ :=
  ∑ i : Fin 64, z i * Complex.exp
    ((s - (1 / 2 : ℂ)) * (fsLogSlice p (ticks i) : ℂ))

/-- Exact Mellin polynomial identity for all complex spectral points. -/
theorem hexagram64_timeSlice_mellin_exact
    (g : WeilCompactSmoothGV1) (p : ℝ)
    (ticks : Fin 64 → ℤ) (z : Fin 64 → ℂ) (s : ℂ) :
    mellin (packetSum z (timeSliceFamily g p ticks)).1 s =
      hexagram64MellinMultiplier p ticks z s * mellin g.1 s := by
  calc
    mellin (packetSum z (timeSliceFamily g p ticks)).1 s =
        ∑ i : Fin 64, z i * mellin (timeSliceFamily g p ticks i).1 s :=
      mellin_packetSum_exact z (timeSliceFamily g p ticks) s
    _ = ∑ i : Fin 64,
        (z i * Complex.exp
          ((s - (1 / 2 : ℂ)) * (fsLogSlice p (ticks i) : ℂ))) *
            mellin g.1 s := by
      apply Finset.sum_congr rfl
      intro i _
      change z i * mellin (timeSlicePacket g p (ticks i)).1 s = _
      rw [timeSlice_mellin]
      ring
    _ = hexagram64MellinMultiplier p ticks z s * mellin g.1 s := by
      unfold hexagram64MellinMultiplier
      rw [Finset.sum_mul]

/-- Full 64-state Walsh projection on the SAME true Mellin packets. -/
theorem hexagram64_walsh_mellin_exact
    (g : WeilCompactSmoothGV1) (p : ℝ)
    (ticks : Fin 64 → ℤ) (a : Fin 64) (s : ℂ) :
    mellin (hexagram64WalshMode (timeSliceFamily g p ticks) a).1 s =
      hexagram64MellinMultiplier p ticks
        (fun i => (hexagramWalsh64 a i : ℂ)) s * mellin g.1 s := by
  change mellin (packetSum (fun i => (hexagramWalsh64 a i : ℂ))
    (timeSliceFamily g p ticks)).1 s = _
  exact hexagram64_timeSlice_mellin_exact g p ticks
    (fun i => (hexagramWalsh64 a i : ℂ)) s

/-- No Walsh or temporal redistribution removes a Mellin zero common to
all translates of the original seed; this enforces the spectral scope. -/
theorem hexagram64_mellin_seed_zero_persists
    (g : WeilCompactSmoothGV1) (p : ℝ)
    (ticks : Fin 64 → ℤ) (z : Fin 64 → ℂ) (s : ℂ)
    (hg : mellin g.1 s = 0) :
    mellin (packetSum z (timeSliceFamily g p ticks)).1 s = 0 := by
  rw [hexagram64_timeSlice_mellin_exact, hg, mul_zero]

/-- The actual multiplicity-weighted zeta-zero summand is the PRODUCT
of the two Mellin polynomials, with no zero-side coefficient omitted. -/
theorem hexagram64_zero_summand_mellin_exact
    (g : WeilCompactSmoothGV1) (p : ℝ)
    (ticks : Fin 64 → ℤ) (z : Fin 64 → ℂ)
    (rho : RiemannNontrivialZeroIndexV2) :
    WeilZeroIndexSummandV1
        (WeilAutocorrelationV1
          (packetSum z (timeSliceFamily g p ticks))) rho =
      (analyticOrderNatAt riemannZeta rho.1 : ℂ) *
        ((hexagram64MellinMultiplier p ticks z rho.1 * mellin g.1 rho.1) *
          conj (hexagram64MellinMultiplier p ticks z (1 - conj rho.1) *
            mellin g.1 (1 - conj rho.1))) := by
  rw [autocorrelation_zero_summand_factorization_v11,
    hexagram64_timeSlice_mellin_exact,
    hexagram64_timeSlice_mellin_exact]

/-- This is genuine Mellin inversion on the entire 64-state sum,
not an approximation to an unspecified source packet. -/
theorem hexagram64_mellin_inversion_exact
    (g : WeilCompactSmoothGV1) (p : ℝ)
    (ticks : Fin 64 → ℤ) (z : Fin 64 → ℂ)
    (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    mellinInv σ (mellin (packetSum z (timeSliceFamily g p ticks)).1) x =
      (packetSum z (timeSliceFamily g p ticks)).1 x := by
  exact weil_compact_smooth_mellin_inversion_v1 _ σ hx

/-- Prime-side Mellin inversion for the SAME sum, including true
von Mangoldt coefficients and the actual zeta logarithmic derivative. -/
theorem hexagram64_prime_line_actual
    (g : WeilCompactSmoothGV1) (p : ℝ)
    (ticks : Fin 64 → ℤ) (z : Fin 64 → ℂ)
    (c : ℝ) (hc : 1 < c) :
    (1 / (2 * Real.pi) : ℝ) •
      (∫ t : ℝ,
        (-deriv riemannZeta ((c : ℂ) + t * I) /
          riemannZeta ((c : ℂ) + t * I)) *
          (hexagram64MellinMultiplier p ticks z ((c : ℂ) + t * I) *
            mellin g.1 ((c : ℂ) + t * I))) =
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
      (packetSum z (timeSliceFamily g p ticks)).1 (n : ℝ) := by
  have h := weil_compact_smooth_prime_line_identity_v1
    (packetSum z (timeSliceFamily g p ticks)) c hc
  simpa only [hexagram64_timeSlice_mellin_exact] using h

/-- Both exact sides live on ONE family: the full actual Weil Gram and
its precisely inverted 64-hexagram Mellin polynomial. -/
theorem hexagram64_mellin_weil_joint_exact
    (g : WeilCompactSmoothGV1) (p : ℝ)
    (ticks : Fin 64 → ℤ) (z : Fin 64 → ℂ) (s : ℂ) :
    (mellin (packetSum z (timeSliceFamily g p ticks)).1 s =
      hexagram64MellinMultiplier p ticks z s * mellin g.1 s) ∧
    (B (packetSum z (timeSliceFamily g p ticks))
       (packetSum z (timeSliceFamily g p ticks)) =
       ∑ i : Fin 64, ∑ j : Fin 64,
         z i * star (z j) *
           B (timeSliceFamily g p ticks i)
             (timeSliceFamily g p ticks j)) := by
  exact ⟨hexagram64_timeSlice_mellin_exact g p ticks z s,
    hexagram64_actual_femtosecond_full_gram g p ticks z⟩

end AEGIS.RHHexagram64MellinWeilFusionV1

#print axioms AEGIS.RHHexagram64MellinWeilFusionV1.mellin_packetSum_exact
#print axioms AEGIS.RHHexagram64MellinWeilFusionV1.every_moment_zero_packet_actual_mellin_weil_zero_fusion
#print axioms AEGIS.RHHexagram64MellinWeilFusionV1.every_moment_zero_packet_actual_prime_line_mellin_fusion
#print axioms AEGIS.RHHexagram64MellinWeilFusionV1.hexagram64_timeSlice_mellin_exact
#print axioms AEGIS.RHHexagram64MellinWeilFusionV1.hexagram64_walsh_mellin_exact
#print axioms AEGIS.RHHexagram64MellinWeilFusionV1.hexagram64_mellin_seed_zero_persists
#print axioms AEGIS.RHHexagram64MellinWeilFusionV1.hexagram64_zero_summand_mellin_exact
#print axioms AEGIS.RHHexagram64MellinWeilFusionV1.hexagram64_mellin_inversion_exact
#print axioms AEGIS.RHHexagram64MellinWeilFusionV1.hexagram64_prime_line_actual
#print axioms AEGIS.RHHexagram64MellinWeilFusionV1.hexagram64_mellin_weil_joint_exact