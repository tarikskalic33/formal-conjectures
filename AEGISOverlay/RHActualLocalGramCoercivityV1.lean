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
import AEGISOverlay.RHFiniteActualGramJoinV1
import RHFineDiagonalUpgradeV3
import RHWindow693Over2000V1

/-!
AEGIS Ω — universal *actual Weil* finite-localization / Gram join.

For EVERY moment-zero Weil packet and EVERY locally complete smooth finite
partition with narrow compact cutoffs, this source constructs genuine
moment-zero Weil components, recovers the original packet EXACTLY, proves
the existing unconditional 32/25 coercive diagonal for EACH component,
and identifies the ENTIRE real arithmetic quadratic with the full finite
Weil Gram matrix, including the mixed terms.

This is not the unconditional RH theorem: it does not assume or claim an
unproved mixed-term sign.  The original source theorem only assumed a
partition summing to 1 on the entire real line, whereas a finite family of
compactly supported cutoffs cannot do that.  Here the partition is required
to sum to 1 only on the compact support interval of the given packet,
exactly as the existing Krein factor decomposition requires.
-/

open Set Finset Complex
open scoped ContDiff BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHActualLocalGramCoercivityV1

open AEGIS.RHKreinFactorV13
open AEGIS.RHLocalKreinPartitionV1
open AEGIS.RHKreinMultiplicativeTransportV1
open AEGIS.RHGramExpansionV13
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2

theorem every_packet_actual_narrow_coercive_gram
    (n : ℕ)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (L : ℝ) (hL : 0 ≤ L)
    (hs : tsupport (lift g.1) ⊆ Icc (-L) L)
    (χ : Fin (n + 1) → ℝ → ℂ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hpart : ∀ x ∈ Icc (-L) L, ∑ i : Fin (n + 1), χ i x = 1)
    (center : Fin (n + 1) → ℝ)
    (hcut : ∀ i, tsupport (χ i) ⊆
      Icc (center i - 1 / 128) (center i + 1 / 128)) :
    ∃ gs : Fin (n + 1) → WeilCompactSmoothGV1,
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∀ i, (32 / 25 : ℝ) * energy (gs i).1 ≤ -(B (gs i) (gs i)).re) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
  classical
  obtain ⟨φ, hφ, hsφ, hsplit, _⟩ :=
    actual_packet_finite_krein_decomposition
      (Finset.univ : Finset (Fin (n + 1))) g hm (-L) L
      (by linarith) hs χ hχ (by
        intro x hx
        simpa using hpart x hx)
  let ψ (i : Fin (n + 1)) : ℝ → ℂ := fun y => χ i y * φ y
  have hψ (i : Fin (n + 1)) : ContDiff ℝ ∞ (ψ i) :=
    (hχ i).mul hφ
  have hψsupp (i : Fin (n + 1)) :
      tsupport (kreinAtom (ψ i)) ⊆ Icc (-L) L :=
    (kreinAtom_support (ψ i)).trans
      ((tsupport_factor_mul (χ i) φ).trans hsφ)
  have hcφ : HasCompactSupport φ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsφ
  have hcψ (i : Fin (n + 1)) : HasCompactSupport (ψ i) := hcφ.mul_left
  let gs (i : Fin (n + 1)) : WeilCompactSmoothGV1 :=
    unliftWeilPacket (kreinAtom (ψ i))
      (kreinAtom_contDiff (ψ i) (hψ i)) (-L) L (hψsupp i)
  have hmom (i : Fin (n + 1)) : WeilMomentConditionsV1 (gs i) :=
    unliftWeilPacket_kreinAtom_moments
      (ψ i) (hψ i) (-L) L (hψsupp i) (hcψ i)
  have hsLocal (i : Fin (n + 1)) :
      tsupport (lift (gs i).1) ⊆ tsupport (χ i) := by
    change tsupport (lift (unlift (kreinAtom (ψ i)))) ⊆ tsupport (χ i)
    rw [lift_unlift]
    have hswap : ψ i = (fun y => φ y * χ i y) := by
      funext y
      dsimp [ψ]
      exact mul_comm (χ i y) (φ y)
    calc
      tsupport (kreinAtom (ψ i)) ⊆ tsupport (ψ i) :=
        kreinAtom_support (ψ i)
      _ = tsupport (fun y => φ y * χ i y) :=
        congrArg tsupport hswap
      _ ⊆ tsupport (χ i) := tsupport_factor_mul φ (χ i)
  have hdiag (i : Fin (n + 1)) :
      (32 / 25 : ℝ) * energy (gs i).1 ≤ -(B (gs i) (gs i)).re := by
    have hw : AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt
        (gs i) (center i) := by
      change tsupport (lift (gs i).1) ⊆
        Icc (center i - 1 / 128) (center i + 1 / 128)
      exact (hsLocal i).trans (hcut i)
    exact AEGIS.RHNarrowDiagonalUpgradeV2.narrow_diagonal_32_over_25_v2
      (gs i) (center i) hw
  have hsum :
      g.1 = (fun x => ∑ i : Fin (n + 1), (gs i).1 x) := by
    have hsplit' :
        lift g.1 =
          (fun x => ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))),
            kreinAtom (ψ i) x) := hsplit
    calc
      g.1 = unlift (lift g.1) := (unlift_lift g).symm
      _ = unlift (fun x => ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))),
            kreinAtom (ψ i) x) := congrArg unlift hsplit'
      _ = (fun x => ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))),
            unlift (kreinAtom (ψ i)) x) :=
              unlift_finset_sum (Finset.univ : Finset (Fin (n + 1)))
                (fun i => kreinAtom (ψ i))
      _ = (fun x => ∑ i : Fin (n + 1), (gs i).1 x) := rfl
  have hpacket : g = packetSum (fun _ => (1 : ℂ)) gs := by
    apply Subtype.ext
    calc
      g.1 = (fun x => ∑ i : Fin (n + 1), (gs i).1 x) := hsum
      _ = (packetSum (fun _ => (1 : ℂ)) gs).1 :=
        (AEGIS.RHFiniteActualGramJoinV1.packetSum_one_apply n gs).symm
  refine ⟨gs, hmom, hdiag, hpacket, ?_⟩
  rw [hpacket]
  change
    (B (packetSum (fun _ => (1 : ℂ)) gs)
       (packetSum (fun _ => (1 : ℂ)) gs)).re =
      (∑ i, ∑ j, B (gs i) (gs j)).re
  rw [B_packetSum]
  simp


/-- A genuinely arbitrary moment-zero packet admits an exact finite
decomposition into width-1/128 actual Weil atoms, for every feasible finite
smooth support-local partition at half-width 1/256. The original PR721
RHFineDiagonalUpgradeV3 proves the stronger diagonal gain 5671/3200 for
EACH atom. The FULL arithmetic Hermitian Gram includes all mixed terms.

This supplies the exact stronger diagonal input required by the historical
eleven-block comparison. It does not assert its 55 cross-coefficient bounds
or the universal sign. -/

theorem every_packet_actual_fine_coercive_gram_with_support_and_cutoff
    (n : ℕ)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (L : ℝ) (hL : 0 ≤ L)
    (hs : tsupport (lift g.1) ⊆ Icc (-L) L)
    (χ : Fin (n + 1) → ℝ → ℂ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hpart : ∀ x ∈ Icc (-L) L, ∑ i : Fin (n + 1), χ i x = 1)
    (center : Fin (n + 1) → ℝ)
    (hcut : ∀ i, tsupport (χ i) ⊆
      Icc (center i - 1 / 256) (center i + 1 / 256)) :
    ∃ gs : Fin (n + 1) → WeilCompactSmoothGV1,
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤ -(B (gs i) (gs i)).re) ∧
      (∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i)) ∧
      (∀ i, tsupport (lift (gs i).1) ⊆ tsupport (χ i)) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
  classical
  obtain ⟨φ, hφ, hsφ, hsplit, _⟩ :=
    actual_packet_finite_krein_decomposition
      (Finset.univ : Finset (Fin (n + 1))) g hm (-L) L
      (by linarith) hs χ hχ (by
        intro x hx
        simpa using hpart x hx)
  let ψ (i : Fin (n + 1)) : ℝ → ℂ := fun y => χ i y * φ y
  have hψ (i : Fin (n + 1)) : ContDiff ℝ ∞ (ψ i) :=
    (hχ i).mul hφ
  have hψsupp (i : Fin (n + 1)) :
      tsupport (kreinAtom (ψ i)) ⊆ Icc (-L) L :=
    (kreinAtom_support (ψ i)).trans
      ((tsupport_factor_mul (χ i) φ).trans hsφ)
  have hcφ : HasCompactSupport φ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsφ
  have hcψ (i : Fin (n + 1)) : HasCompactSupport (ψ i) := hcφ.mul_left
  let gs (i : Fin (n + 1)) : WeilCompactSmoothGV1 :=
    unliftWeilPacket (kreinAtom (ψ i))
      (kreinAtom_contDiff (ψ i) (hψ i)) (-L) L (hψsupp i)
  have hmom (i : Fin (n + 1)) : WeilMomentConditionsV1 (gs i) :=
    unliftWeilPacket_kreinAtom_moments
      (ψ i) (hψ i) (-L) L (hψsupp i) (hcψ i)
  have hsLocal (i : Fin (n + 1)) :
      tsupport (lift (gs i).1) ⊆ tsupport (χ i) := by
    change tsupport (lift (unlift (kreinAtom (ψ i)))) ⊆ tsupport (χ i)
    rw [lift_unlift]
    have hswap : ψ i = (fun y => φ y * χ i y) := by
      funext y
      dsimp [ψ]
      exact mul_comm (χ i y) (φ y)
    calc
      tsupport (kreinAtom (ψ i)) ⊆ tsupport (ψ i) :=
        kreinAtom_support (ψ i)
      _ = tsupport (fun y => φ y * χ i y) :=
        congrArg tsupport hswap
      _ ⊆ tsupport (χ i) := tsupport_factor_mul φ (χ i)
  have hwidth (i : Fin (n + 1)) :
      AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i) := by
    change tsupport (lift (gs i).1) ⊆
      Icc (center i - 1 / 256) (center i + 1 / 256)
    exact (hsLocal i).trans (hcut i)
  have hdiag (i : Fin (n + 1)) :
      (5671 / 3200 : ℝ) * energy (gs i).1 ≤ -(B (gs i) (gs i)).re := by
    have hw : AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i) := by
      change tsupport (lift (gs i).1) ⊆
        Icc (center i - 1 / 256) (center i + 1 / 256)
      exact (hsLocal i).trans (hcut i)
    exact AEGIS.RHFineDiagonalUpgradeV3.fine_diagonal_5671_over_3200_v3
      (gs i) (center i) hw
  have hsum :
      g.1 = (fun x => ∑ i : Fin (n + 1), (gs i).1 x) := by
    have hsplit' :
        lift g.1 =
          (fun x => ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))),
            kreinAtom (ψ i) x) := hsplit
    calc
      g.1 = unlift (lift g.1) := (unlift_lift g).symm
      _ = unlift (fun x => ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))),
            kreinAtom (ψ i) x) := congrArg unlift hsplit'
      _ = (fun x => ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))),
            unlift (kreinAtom (ψ i)) x) :=
              unlift_finset_sum (Finset.univ : Finset (Fin (n + 1)))
                (fun i => kreinAtom (ψ i))
      _ = (fun x => ∑ i : Fin (n + 1), (gs i).1 x) := rfl
  have hpacket : g = packetSum (fun _ => (1 : ℂ)) gs := by
    apply Subtype.ext
    calc
      g.1 = (fun x => ∑ i : Fin (n + 1), (gs i).1 x) := hsum
      _ = (packetSum (fun _ => (1 : ℂ)) gs).1 :=
        (AEGIS.RHFiniteActualGramJoinV1.packetSum_one_apply n gs).symm
  refine ⟨gs, hmom, hdiag, hwidth, hsLocal, hpacket, ?_⟩
  rw [hpacket]
  change
    (B (packetSum (fun _ => (1 : ℂ)) gs)
       (packetSum (fun _ => (1 : ℂ)) gs)).re =
      (∑ i, ∑ j, B (gs i) (gs j)).re
  rw [B_packetSum]
  simp



/-- Preserve the original fine-support API while keeping the exact cutoff
inclusion available to downstream horizon-sensitive assembly. -/
theorem every_packet_actual_fine_coercive_gram_with_support
    (n : ℕ)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (L : ℝ) (hL : 0 ≤ L)
    (hs : tsupport (lift g.1) ⊆ Icc (-L) L)
    (χ : Fin (n + 1) → ℝ → ℂ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hpart : ∀ x ∈ Icc (-L) L, ∑ i : Fin (n + 1), χ i x = 1)
    (center : Fin (n + 1) → ℝ)
    (hcut : ∀ i, tsupport (χ i) ⊆
      Icc (center i - 1 / 256) (center i + 1 / 256)) :
    ∃ gs : Fin (n + 1) → WeilCompactSmoothGV1,
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤ -(B (gs i) (gs i)).re) ∧
      (∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i)) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
  obtain ⟨gs, hmom, hdiag, hwidth, _, hpacket, hgram⟩ :=
    every_packet_actual_fine_coercive_gram_with_support_and_cutoff
      n g hm L hL hs χ hχ hpart center hcut
  exact ⟨gs, hmom, hdiag, hwidth, hpacket, hgram⟩

/-- Exact-radius actual finite Krein/Weil Gram from any subordinate
fine partition. This theorem does not claim mixed-row estimates. -/
theorem every_packet_actual_fine_coercive_gram_at_radius
    (n : ℕ)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (L : ℝ) (hL : 0 ≤ L)
    (hs : tsupport (lift g.1) ⊆ Icc (-L) L)
    (χ : Fin (n + 1) → ℝ → ℂ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hpart : ∀ x ∈ Icc (-L) L, ∑ i : Fin (n + 1), χ i x = 1)
    (center : Fin (n + 1) → ℝ)
    (r : ℝ) (_hr0 : 0 ≤ r) (hrFine : r ≤ 1 / 256)
    (hcut : ∀ i, tsupport (χ i) ⊆
      Icc (center i - r) (center i + r)) :
    ∃ gs : Fin (n + 1) → WeilCompactSmoothGV1,
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
        -(B (gs i) (gs i)).re) ∧
      (∀ i, AEGIS.RHDyadicDiagonalV13.HalfWidthAt
        (gs i) r (center i)) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
  have hcutFine : ∀ i, tsupport (χ i) ⊆
      Icc (center i - 1 / 256) (center i + 1 / 256) := by
    intro i x hx
    obtain ⟨hlo, hhi⟩ := hcut i hx
    exact ⟨by linarith, by linarith⟩
  obtain ⟨gs, hmom, hdiag, _, hsLocal, hpacket, hgram⟩ :=
    every_packet_actual_fine_coercive_gram_with_support_and_cutoff
      n g hm L hL hs χ hχ hpart center hcutFine
  refine ⟨gs, hmom, hdiag, ?_, hpacket, hgram⟩
  intro i
  change tsupport (lift (gs i).1) ⊆
    Icc (center i - r) (center i + r)
  exact (hsLocal i).trans (hcut i)

/-- Preserve the original interface while the stronger producer retains support witnesses. -/
theorem every_packet_actual_fine_coercive_gram
    (n : ℕ)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (L : ℝ) (hL : 0 ≤ L)
    (hs : tsupport (lift g.1) ⊆ Icc (-L) L)
    (χ : Fin (n + 1) → ℝ → ℂ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hpart : ∀ x ∈ Icc (-L) L, ∑ i : Fin (n + 1), χ i x = 1)
    (center : Fin (n + 1) → ℝ)
    (hcut : ∀ i, tsupport (χ i) ⊆
      Icc (center i - 1 / 256) (center i + 1 / 256)) :
    ∃ gs : Fin (n + 1) → WeilCompactSmoothGV1,
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤ -(B (gs i) (gs i)).re) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
  obtain ⟨gs, hmom, hd, _, hpacket, hgram⟩ :=
    every_packet_actual_fine_coercive_gram_with_support
      n g hm L hL hs χ hχ hpart center hcut
  exact ⟨gs, hmom, hd, hpacket, hgram⟩


/-- For a packet in the *already certified* 693/2000 log-window, any
finite smooth partition summing to one only on its support produces
genuine localized moment-zero Weil packets with coercive diagonals and
a nonpositive FULL mixed Gram contraction. No mixed term is discarded.

The narrow-window hypothesis applies to the original packet; the theorem
does not assert that arbitrary linear combinations of the localized atoms
have this window, nor that their full Gram matrix is negative semidefinite. -/
theorem every_narrow_packet_actual_localized_full_gram_nonpositive
    (n : ℕ)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (hw : AEGIS.WeilWindowExhaustionV1.LogWindowContainsV1 g (693 / 2000))
    (L : ℝ) (hL : 0 ≤ L)
    (hs : tsupport (lift g.1) ⊆ Icc (-L) L)
    (χ : Fin (n + 1) → ℝ → ℂ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hpart : ∀ x ∈ Icc (-L) L, ∑ i : Fin (n + 1), χ i x = 1)
    (center : Fin (n + 1) → ℝ)
    (hcut : ∀ i, tsupport (χ i) ⊆
      Icc (center i - 1 / 128) (center i + 1 / 128)) :
    ∃ gs : Fin (n + 1) → WeilCompactSmoothGV1,
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∀ i, (32 / 25 : ℝ) * energy (gs i).1 ≤ -(B (gs i) (gs i)).re) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (∑ i, ∑ j, B (gs i) (gs j)).re ≤ 0 := by
  obtain ⟨gs, hmom, hdiag, hpacket, hfull⟩ :=
    every_packet_actual_narrow_coercive_gram
      n g hm L hL hs χ hχ hpart center hcut
  refine ⟨gs, hmom, hdiag, hpacket, ?_⟩
  calc
    (∑ i, ∑ j, B (gs i) (gs j)).re =
        (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re := hfull.symm
    _ ≤ 0 :=
      AEGIS.RHWindow693Over2000V1.window_693_over_2000_arithmetic_nonpositive_v1
        g hm hw

end AEGIS.RHActualLocalGramCoercivityV1

#print axioms AEGIS.RHActualLocalGramCoercivityV1.every_packet_actual_narrow_coercive_gram
#print axioms AEGIS.RHActualLocalGramCoercivityV1.every_packet_actual_fine_coercive_gram
#print axioms AEGIS.RHActualLocalGramCoercivityV1.every_narrow_packet_actual_localized_full_gram_nonpositive

#print axioms AEGIS.RHActualLocalGramCoercivityV1.every_packet_actual_fine_coercive_gram_with_support_and_cutoff
#print axioms AEGIS.RHActualLocalGramCoercivityV1.every_packet_actual_fine_coercive_gram_at_radius
#print axioms AEGIS.RHActualLocalGramCoercivityV1.every_packet_actual_fine_coercive_gram_with_support
