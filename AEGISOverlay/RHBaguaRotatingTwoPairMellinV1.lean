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
import AEGISOverlay.RHFourLogThreeActualPrimeV1
import AEGISOverlay.RHBaguaActualWeilV1
import AEGISOverlay.RHTimeSliceWeilV1
import Mathlib.Tactic

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHBaguaRotatingTwoPairMellinV1

open AEGIS.RHGramExpansionV13
open AEGIS.RHActualNarrowGramSignV1
open AEGIS.RHBaguaActualWeilV1
open AEGIS.RHFourLogThreeActualPrimeV1
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilZeroTranslationV11
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHDyadicDiagonalV13

def quarterTurnPhase (q : Fin 4) : ℂ := Complex.I ^ q.val

def rotatingBaguaCoeff (z : Fin 8 → ℂ) (q : Fin 4)
    (i : Fin 8) : ℂ :=
  baguaPlus z i + quarterTurnPhase q * baguaMinus z i

theorem rotatingBaguaCoeff_opposite
    (z : Fin 8 → ℂ) (q : Fin 4) (i : Fin 8) :
    rotatingBaguaCoeff z q (baguaOpp i) =
      baguaPlus z i - quarterTurnPhase q * baguaMinus z i := by
  simp only [rotatingBaguaCoeff, baguaPlus_even, baguaMinus_odd]
  ring

theorem rotating_bagua_two_moments
    (gs : Fin 8 → WeilCompactSmoothGV1)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (z : Fin 8 → ℂ) (q : Fin 4) :
    WeilMomentConditionsV1
      (packetSum (rotatingBaguaCoeff z q) gs) := by
  exact AEGIS.RHActualNarrowGramSignV1.trigram_moment_packetSum
    7 (rotatingBaguaCoeff z q) gs hm

theorem rotating_bagua_complementary_moments
    (gs : Fin 8 → WeilCompactSmoothGV1)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (z : Fin 8 → ℂ) (q : Fin 4) :
    WeilMomentConditionsV1
      (baguaEvenPacket gs (rotatingBaguaCoeff z q)) ∧
    WeilMomentConditionsV1
      (baguaOddPacket gs (rotatingBaguaCoeff z q)) := by
  exact AEGIS.RHBaguaActualWeilV1.bagua_both_complementary_moments
    gs (rotatingBaguaCoeff z q) hm

theorem rotating_bagua_four_block_exact
    (gs : Fin 8 → WeilCompactSmoothGV1)
    (z : Fin 8 → ℂ) (q : Fin 4) :
    B (packetSum (rotatingBaguaCoeff z q) gs)
      (packetSum (rotatingBaguaCoeff z q) gs) =
      ∑ i : Fin 8, ∑ j : Fin 8,
        (baguaPlus z i * star (baguaPlus z j) +
          baguaPlus z i *
            star (quarterTurnPhase q * baguaMinus z j) +
          (quarterTurnPhase q * baguaMinus z i) *
            star (baguaPlus z j) +
          (quarterTurnPhase q * baguaMinus z i) *
            star (quarterTurnPhase q * baguaMinus z j)) *
          B (gs i) (gs j) := by
  rw [B_packetSum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [rotatingBaguaCoeff, star_add]
  ring

theorem rotating_bagua_actual_atom_mellin
    (gs : Fin 8 → WeilCompactSmoothGV1)
    (center : Fin 8 → ℝ)
    (g : WeilCompactSmoothGV1)
    (hfamily : ∀ i, gs i = translatePacket g (center i))
    (s : ℂ) (i : Fin 8) :
    mellin (gs i).1 s =
      Complex.exp ((s - (1 / 2 : ℂ)) * (center i : ℂ)) *
        mellin g.1 s := by
  rw [hfamily i]
  exact mellin_translatePacket_v11 g (center i) s

theorem rotating_bagua_fs_atom_mellin
    (g : WeilCompactSmoothGV1) (p : ℝ)
    (ticks : Fin 8 → ℤ) (s : ℂ) (i : Fin 8) :
    mellin (AEGIS.RHTimeSliceWeilV1.timeSliceEight g p ticks i).1 s =
      Complex.exp ((s - (1 / 2 : ℂ)) *
        (AEGIS.RHTimeSliceWeilV1.fsLogSlice p (ticks i) : ℂ)) *
          mellin g.1 s := by
  exact AEGIS.RHTimeSliceWeilV1.timeSlice_mellin
    g s p (ticks i)

theorem rotating_bagua_four_phase_mellin_weil_coercive
    (gs : Fin 8 → WeilCompactSmoothGV1)
    (center : Fin 8 → ℝ)
    (hwidth : ∀ i,
      AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i))
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hsep : ∀ i j : Fin 8, i < j →
      1 ≤ Nat.dist i j ∧
        (65 / 32 : ℝ) * (Nat.dist i j : ℝ) ≤ center j - center i)
    (K : ℕ) (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a)
    (hfamily : ∀ i, gs i = translatePacket g (center i))
    (hgap : ∀ i j : Fin 8, i < j →
      4 * Nat.dist i j ≤ K ∧
        center j - center i =
          ((4 * Nat.dist i j : ℕ) : ℝ) * Real.log 3)
    (s : ℂ) (z : Fin 8 → ℂ) :
    (∀ i, mellin (gs i).1 s =
      Complex.exp ((s - (1 / 2 : ℂ)) * (center i : ℂ)) *
        mellin g.1 s) ∧
    (∀ q : Fin 4,
      WeilMomentConditionsV1
        (packetSum (rotatingBaguaCoeff z q) gs) ∧
      (B (packetSum (rotatingBaguaCoeff z q) gs)
        (packetSum (rotatingBaguaCoeff z q) gs)).re ≤
        -(641 / 32768 : ℝ) *
          (∑ i, energy (gs i).1 *
            ‖rotatingBaguaCoeff z q i‖ ^ 2)) := by
  constructor
  · intro i
    exact rotating_bagua_actual_atom_mellin gs center g hfamily s i
  · intro q
    constructor
    · exact rotating_bagua_two_moments gs hm z q
    · exact actual_four_log_three_weighted_norm_coercive
        gs center hwidth hm hsep K g a hw hfamily hgap
          (rotatingBaguaCoeff z q)

theorem rotating_bagua_two_point_mellin_and_moments
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (d : ℝ) (s : ℂ) (q : Fin 4) :
    WeilMomentConditionsV1
      (AEGIS.WeilZeroTwoPointV11.WeilTwoPointTranslateV11
        g d (quarterTurnPhase q)) ∧
    mellin (AEGIS.WeilZeroTwoPointV11.WeilTwoPointTranslateV11
      g d (quarterTurnPhase q)).1 s =
      (1 + quarterTurnPhase q *
        Complex.exp ((s - (1 / 2 : ℂ)) * (d : ℂ))) *
          mellin g.1 s := by
  constructor
  · exact AEGIS.WeilZeroKernelHermitianV11.twoPointTranslate_preserves_moments_v11
      g d (quarterTurnPhase q) hm
  · exact AEGIS.WeilZeroTwoPointV11.mellin_twoPointTranslate_v11
      g d (quarterTurnPhase q) s

theorem rotating_bagua_two_pair_four_phase_mellin_join
    (gs : Fin 8 → WeilCompactSmoothGV1)
    (center : Fin 8 → ℝ)
    (hwidth : ∀ i,
      AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i))
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hsep : ∀ i j : Fin 8, i < j →
      1 ≤ Nat.dist i j ∧
        (65 / 32 : ℝ) * (Nat.dist i j : ℝ) ≤ center j - center i)
    (K : ℕ) (g : WeilCompactSmoothGV1) (a : ℝ)
    (hmg : WeilMomentConditionsV1 g)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a)
    (hfamily : ∀ i, gs i = translatePacket g (center i))
    (hgap : ∀ i j : Fin 8, i < j →
      4 * Nat.dist i j ≤ K ∧
        center j - center i =
          ((4 * Nat.dist i j : ℕ) : ℝ) * Real.log 3)
    (s : ℂ) (z : Fin 8 → ℂ) :
    (∀ i, mellin (gs i).1 s =
      Complex.exp ((s - (1 / 2 : ℂ)) * (center i : ℂ)) *
        mellin g.1 s) ∧
    (∀ q : Fin 4,
      WeilMomentConditionsV1
        (packetSum (rotatingBaguaCoeff z q) gs) ∧
      (B (packetSum (rotatingBaguaCoeff z q) gs)
        (packetSum (rotatingBaguaCoeff z q) gs)).re ≤
        -(641 / 32768 : ℝ) *
          (∑ i, energy (gs i).1 *
            ‖rotatingBaguaCoeff z q i‖ ^ 2) ∧
      (WeilMomentConditionsV1
        (baguaEvenPacket gs (rotatingBaguaCoeff z q)) ∧
       WeilMomentConditionsV1
        (baguaOddPacket gs (rotatingBaguaCoeff z q))) ∧
      (WeilMomentConditionsV1
        (AEGIS.WeilZeroTwoPointV11.WeilTwoPointTranslateV11
          g (4 * Real.log 3) (quarterTurnPhase q)) ∧
       mellin (AEGIS.WeilZeroTwoPointV11.WeilTwoPointTranslateV11
         g (4 * Real.log 3) (quarterTurnPhase q)).1 s =
         (1 + quarterTurnPhase q *
           Complex.exp ((s - (1 / 2 : ℂ)) *
             ((4 * Real.log 3 : ℝ) : ℂ))) *
           mellin g.1 s)) := by
  have hbase := rotating_bagua_four_phase_mellin_weil_coercive
    gs center hwidth hm hsep K g a hw hfamily hgap s z
  constructor
  · exact hbase.1
  · intro q
    obtain ⟨hpacket, hbound⟩ := hbase.2 q
    exact ⟨hpacket, hbound,
      rotating_bagua_complementary_moments gs hm z q,
      rotating_bagua_two_point_mellin_and_moments
        g hmg (4 * Real.log 3) s q⟩

theorem rotating_bagua_phase_zero (z : Fin 8 → ℂ) (i : Fin 8) :
    rotatingBaguaCoeff z (0 : Fin 4) i = z i := by
  simpa [rotatingBaguaCoeff, quarterTurnPhase] using
    (bagua_reconstruct z i)

theorem actual_sparse_walsh_bagua_mode_negative
    (gs : Fin 8 → WeilCompactSmoothGV1)
    (center : Fin 8 → ℝ)
    (hwidth : ∀ i,
      AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i))
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hsep : ∀ i j : Fin 8, i < j →
      1 ≤ Nat.dist i j ∧
        (65 / 32 : ℝ) * (Nat.dist i j : ℝ) ≤ center j - center i)
    (K : ℕ) (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a)
    (hfamily : ∀ i, gs i = translatePacket g (center i))
    (hgap : ∀ i j : Fin 8, i < j →
      4 * Nat.dist i j ≤ K ∧
        center j - center i =
          ((4 * Nat.dist i j : ℕ) : ℝ) * Real.log 3)
    (mode : Fin 8) :
    (B (baguaMode gs mode) (baguaMode gs mode)).re ≤
      -(641 / 32768 : ℝ) *
        (∑ i, energy (gs i).1 *
          ‖(AEGIS.RHBaguaWalshV1.walsh8 mode i : ℂ)‖ ^ 2) := by
  simpa only [baguaMode] using
    (actual_four_log_three_weighted_norm_coercive
      gs center hwidth hm hsep K g a hw hfamily hgap
        (fun i => (AEGIS.RHBaguaWalshV1.walsh8 mode i : ℂ)))

end AEGIS.RHBaguaRotatingTwoPairMellinV1

#print axioms AEGIS.RHBaguaRotatingTwoPairMellinV1.rotatingBaguaCoeff_opposite
#print axioms AEGIS.RHBaguaRotatingTwoPairMellinV1.rotating_bagua_two_moments
#print axioms AEGIS.RHBaguaRotatingTwoPairMellinV1.rotating_bagua_complementary_moments
#print axioms AEGIS.RHBaguaRotatingTwoPairMellinV1.rotating_bagua_four_block_exact
#print axioms AEGIS.RHBaguaRotatingTwoPairMellinV1.rotating_bagua_actual_atom_mellin
#print axioms AEGIS.RHBaguaRotatingTwoPairMellinV1.rotating_bagua_fs_atom_mellin
#print axioms AEGIS.RHBaguaRotatingTwoPairMellinV1.rotating_bagua_four_phase_mellin_weil_coercive
#print axioms AEGIS.RHBaguaRotatingTwoPairMellinV1.rotating_bagua_two_point_mellin_and_moments
#print axioms AEGIS.RHBaguaRotatingTwoPairMellinV1.rotating_bagua_two_pair_four_phase_mellin_join
#print axioms AEGIS.RHBaguaRotatingTwoPairMellinV1.rotating_bagua_phase_zero
#print axioms AEGIS.RHBaguaRotatingTwoPairMellinV1.actual_sparse_walsh_bagua_mode_negative
