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

import RHKreinMultiplicativeTransportV1
import RHGramExpansionV13
import RHNarrowDiagonalUpgradeV2
import Mathlib

/-!
# AEGIS Ω: actual finite Krein atoms to actual Weil Gram matrix

This integrates two pre-existing, *unconditional* source theorems:
1. Every moment-zero packet has an exact finite decomposition into genuine
   moment-zero Weil packets for each smooth finite partition of unity.
2. The actual sesquilinear Weil form B of a packetSum is its exact finite
   Hermitian Gram matrix, including every off-diagonal/mixed term.

This closes the representation/identity interface only. It makes no claim
that the arbitrary finite Gram matrix has the requisite sign or that any
row-sum, Schur, or cofinal estimate is unconditionally certified.
AUTHORITY_EFFECT = NONE; RH_PROVEN = FALSE.
-/

open Set Finset Complex
open scoped ContDiff BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHFiniteActualGramJoinV1

open AEGIS.RHKreinFactorV13
open AEGIS.RHLocalKreinPartitionV1
open AEGIS.RHKreinMultiplicativeTransportV1
open AEGIS.RHGramExpansionV13
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2

/-- The existing recursively-defined `packetSum` is exactly the pointwise
sum of its genuine packets when all coefficients are 1. -/
theorem packetSum_one_apply :
    ∀ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
      (packetSum (fun _ => (1 : ℂ)) gs).1 =
        (fun x => ∑ i, (gs i).1 x) := by
  intro n
  induction n with
  | zero =>
      intro gs
      funext x
      simp [packetSum, scalePacket]
  | succ n ih =>
      intro gs
      funext x
      have hprev := congrFun (ih (fun i : Fin (n + 1) => gs i.castSucc)) x
      change
        (packetSum (fun _ => (1 : ℂ))
          (fun i : Fin (n + 1) => gs i.castSucc)).1 x +
          (1 : ℂ) * (gs (Fin.last (n + 1))).1 x =
        ∑ i : Fin (n + 2), (gs i).1 x
      rw [Fin.sum_univ_castSucc]
      simpa only [one_mul] using
        congrArg (fun t : ℂ => t + (gs (Fin.last (n + 1))).1 x) hprev

/-- Every moment-zero packet, for *any* smooth finite partition of unity,
is exactly a true Weil Gram quadratic of actual packets. This theorem does
not discard the mixed B terms or replace the actual Weil form by a surrogate. -/
theorem every_packet_actual_finite_gram
    (n : ℕ) (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (χ : Fin (n + 1) → ℝ → ℂ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hpart : ∀ x : ℝ, ∑ i : Fin (n + 1), χ i x = 1) :
    ∃ gs : Fin (n + 1) → WeilCompactSmoothGV1,
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
  classical
  obtain ⟨gs, hgs, hsum⟩ :=
    every_moment_zero_packet_finite_actual_weil_partition
      (Finset.univ : Finset (Fin (n + 1))) g hm χ hχ (by
        intro x
        simpa using hpart x)
  refine ⟨gs, ?_, ?_⟩
  · intro i
    exact hgs i (Finset.mem_univ i)
  · have hpacket : g = packetSum (fun _ => (1 : ℂ)) gs := by
      apply Subtype.ext
      calc
        g.1 = (fun x => ∑ i, (gs i).1 x) := by simpa using hsum
        _ = (packetSum (fun _ => (1 : ℂ)) gs).1 :=
          (packetSum_one_apply n gs).symm
    rw [hpacket]
    change
      (B (packetSum (fun _ => (1 : ℂ)) gs)
        (packetSum (fun _ => (1 : ℂ)) gs)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re
    rw [B_packetSum]
    simp

/-- Localizing a smooth Krein factor with a smooth cutoff produces an
actual compact-smooth Weil packet with both moments zero. Crucially, the
resulting log-support stays inside the *cutoff* support, not merely the
original potentially wide factor support. Thus genuine finite Gram
decompositions can be paired with existing narrow-window producers.
No cross-term positivity is asserted. -/
theorem localized_actual_weil_krein_atom
    (φ χ : ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hχ : ContDiff ℝ ∞ χ)
    (a b : ℝ)
    (hsφ : tsupport φ ⊆ Icc a b) :
    ∃ p : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 p ∧
      tsupport (lift p.1) ⊆ tsupport χ ∧
      lift p.1 = kreinAtom (fun x => χ x * φ x) := by
  let ψ : ℝ → ℂ := fun x => χ x * φ x
  have hψ : ContDiff ℝ ∞ ψ := hχ.mul hφ
  have hsψ : tsupport (kreinAtom ψ) ⊆ Icc a b :=
    (kreinAtom_support ψ).trans
      ((tsupport_factor_mul χ φ).trans hsφ)
  have hcφ : HasCompactSupport φ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsφ
  let p : WeilCompactSmoothGV1 :=
    unliftWeilPacket (kreinAtom ψ) (kreinAtom_contDiff ψ hψ) a b hsψ
  refine ⟨p, ?_, ?_, ?_⟩
  · exact unliftWeilPacket_kreinAtom_moments
      ψ hψ a b hsψ hcφ.mul_left
  · change tsupport (lift (unlift (kreinAtom ψ))) ⊆ tsupport χ
    rw [lift_unlift]
    have hswap : ψ = (fun x => φ x * χ x) := by
      funext x
      exact mul_comm (χ x) (φ x)
    calc
      tsupport (kreinAtom ψ) ⊆ tsupport ψ :=
        kreinAtom_support ψ
      _ = tsupport (fun x => φ x * χ x) :=
        congrArg tsupport hswap
      _ ⊆ tsupport χ := tsupport_factor_mul φ χ
  · change lift (unlift (kreinAtom ψ)) = kreinAtom ψ
    exact lift_unlift (kreinAtom ψ)

/-- Unconditional coercive *diagonal* estimate for every actual localized
Krein atom whose smooth cutoff has logarithmic half-width at most 1/128.
This binds the universal localization producer to the pre-existing
narrow-support arithmetic B certificate, at any center, with no sign
hypothesis and no discarded mixed terms. -/
theorem localized_actual_weil_diagonal_32_over_25
    (φ χ : ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hχ : ContDiff ℝ ∞ χ)
    (a b center : ℝ)
    (hsφ : tsupport φ ⊆ Icc a b)
    (hcut : tsupport χ ⊆ Icc (center - 1 / 128) (center + 1 / 128)) :
    ∃ p : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 p ∧
      lift p.1 = kreinAtom (fun x => χ x * φ x) ∧
      (32 / 25 : ℝ) * energy p.1 ≤ -(B p p).re := by
  obtain ⟨p, hm, hsupport, hfactor⟩ :=
    localized_actual_weil_krein_atom φ χ hφ hχ a b hsφ
  refine ⟨p, hm, hfactor, ?_⟩
  have hw : AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt p center := by
    change tsupport (lift p.1) ⊆
      Icc (center - 1 / 128) (center + 1 / 128)
    exact hsupport.trans hcut
  exact AEGIS.RHNarrowDiagonalUpgradeV2.narrow_diagonal_32_over_25_v2
    p center hw

end AEGIS.RHFiniteActualGramJoinV1

#print axioms AEGIS.RHFiniteActualGramJoinV1.packetSum_one_apply
#print axioms AEGIS.RHFiniteActualGramJoinV1.every_packet_actual_finite_gram
#print axioms AEGIS.RHFiniteActualGramJoinV1.localized_actual_weil_krein_atom
#print axioms AEGIS.RHFiniteActualGramJoinV1.localized_actual_weil_diagonal_32_over_25
