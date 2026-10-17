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
import AEGISOverlay.RHPrimeFreeRecompositionJoinV1
import Mathlib.Tactic
import WeilTranslationGapInvariantV10
import AEGISOverlay.RHArchRow29V1

/-!
# Exact signed prime cost at every four-log-three separation

This is a genuine von Mangoldt (not surrogate Gram) estimate at every
positive lattice displacement d, for any horizon K >= 4*d and an actual
fine packet of the existing K-dependent support.

It does not assume RH, a Schur signed-row certificate, or a selected
reconstruction of arbitrary packets. No claim about a fixed positive
seed radius uniformly in K is made.
-/

open Complex
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHPrimeThreeWindowV1
open AEGIS.RHDyadicDiagonalV13

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHFourLogThreeActualPrimeV1

open AEGIS.RHGramExpansionV13

/-- The exact arithmetic ratio for a 4*d*log(3) gap. -/
theorem triadicHalf_four_mul (d : ℕ) :
    triadicHalf (4 * d) = (1 / 9 : ℝ) ^ d := by
  unfold triadicHalf
  have harg :
      -(((4 * d : ℕ) : ℝ) * Real.log 3) / 2 =
        (d : ℝ) * (-2 * Real.log 3) := by
    push_cast
    ring
  rw [harg, Real.exp_nat_mul]
  have hexp : Real.exp (-2 * Real.log (3 : ℝ)) = (1 / 9 : ℝ) := by
    rw [show -2 * Real.log (3 : ℝ) = -(Real.log 3 + Real.log 3) by ring,
      Real.exp_neg, Real.exp_add]
    norm_num [Real.exp_log]
  rw [hexp]

/-- Actual exact signed prime interaction for every positive 4*d gap. -/
theorem actual_prime_four_log_three_exact
    (K d : ℕ) (hd : 1 ≤ d) (hdK : 4 * d ≤ K)
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a) :
    (WeilPrimeSumV1
      (mixed (translatePacket g 0)
        (translatePacket g ((4 * d : ℕ) * Real.log 3)))).re =
      Real.log 3 * (1 / 9 : ℝ) ^ d * energy g.1 := by
  have hp :=
    AEGIS.RHOptimizedSchurGlobalJoinV1.exact_von_mangoldt_time_horizon
      K (4 * d) (by omega) hdK g a hw
  have hr := congrArg Complex.re hp
  simp only [Complex.ofReal_re] at hr
  simpa only [triadicHalf_four_mul] using hr

/-- Source-proved, uniform-in-d rational cost for the actual prime row
at any separated same-mother pair. No fabricated sign/cross hypotheses. -/
theorem actual_prime_four_log_three_signed_cost
    (K d : ℕ) (hd : 1 ≤ d) (hdK : 4 * d ≤ K)
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a) :
    (WeilPrimeSumV1
      (mixed (translatePacket g 0)
        (translatePacket g ((4 * d : ℕ) * Real.log 3)))).re ≤
      (1 / 9 : ℝ) ^ d *
        (energy (translatePacket g 0).1 +
         energy (translatePacket g ((4 * d : ℕ) * Real.log 3)).1) := by
  have hpow : 0 ≤ (1 / 9 : ℝ) ^ d := by positivity
  have hE : 0 ≤ energy g.1 := energy_nonnegative g.1
  have hcoeff :
      Real.log (3 : ℝ) * ((1 / 9 : ℝ) ^ d * energy g.1) ≤
        2 * ((1 / 9 : ℝ) ^ d * energy g.1) :=
    mul_le_mul_of_nonneg_right
      AEGIS.RHLogThreeSignedPrimeProducerV1.log_three_le_two
      (mul_nonneg hpow hE)
  calc
    (WeilPrimeSumV1
      (mixed (translatePacket g 0)
        (translatePacket g ((4 * d : ℕ) * Real.log 3)))).re =
        Real.log 3 * (1 / 9 : ℝ) ^ d * energy g.1 :=
          actual_prime_four_log_three_exact K d hd hdK g a hw
    _ = Real.log 3 * ((1 / 9 : ℝ) ^ d * energy g.1) := by ring
    _ ≤ 2 * ((1 / 9 : ℝ) ^ d * energy g.1) := hcoeff
    _ = (1 / 9 : ℝ) ^ d *
        (energy (translatePacket g 0).1 +
         energy (translatePacket g ((4 * d : ℕ) * Real.log 3)).1) := by
        rw [translate_energy, translate_energy]
        ring


/-- Uniform rational prime-row estimate for EVERY number of translated
same-mother atoms. Unlike finite 4-block row enumeration, n is arbitrary.
This is the actual geometric budget consumed by Arch-29, not an RH claim. -/
theorem full_four_log_three_prime_row {n : ℕ} (i : Fin (n + 1)) :
    (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
      (1 / 9 : ℝ) ^ Nat.dist i j) ≤ (1 / 4 : ℝ) := by
  have hIcc : (Finset.Icc 1 n : Finset ℕ) =
      Finset.Ico 1 (n + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hgeom :
      (∑ k ∈ Finset.Icc 1 n, (1 / 9 : ℝ) ^ k) ≤
        (1 / 8 : ℝ) := by
    rw [hIcc]
    exact AEGIS.RHOptimizedSchurGlobalJoinV1.four_log_three_prime_geometric_tail n
  have hrow := AEGIS.RHGramExpansionV13.rowSum_le
    (n := n) (c := fun k => (1 / 9 : ℝ) ^ k)
    (by intro k; positivity) i
  calc
    (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        (1 / 9 : ℝ) ^ Nat.dist i j) ≤
      2 * (∑ k ∈ Finset.Icc 1 n, (1 / 9 : ℝ) ^ k) := hrow
    _ ≤ 2 * (1 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_left hgeom (by norm_num)
    _ = 1 / 4 := by norm_num

/-- The genuine signed-prime geometric row fits inside the pre-existing
Arch-29 Schur allowance, uniformly in n. -/
theorem full_four_log_three_prime_row_arch29 {n : ℕ} (i : Fin (n + 1)) :
    (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
      (1 / 9 : ℝ) ^ Nat.dist i j) ≤ (57401 / 65536 : ℝ) :=
  (full_four_log_three_prime_row i).trans (by norm_num)

/-- Actual complex Weil B interaction at every positive four-log-three
gap under the source-bound time-horizon support and moment conditions.
This is not just the prime row: it retains the Archimedean allowance. -/
theorem actual_mixed_B_norm_four_log_three
    (K d : ℕ) (hd : 1 ≤ d) (hdK : 4 * d ≤ K)
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hm : WeilMomentConditionsV1 g)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a) :
    ‖B (translatePacket g 0)
      (translatePacket g ((4 * d : ℕ) * Real.log 3))‖ ≤
      (Real.log 3 * (1 / 9 : ℝ) ^ d + 1 / 100) * energy g.1 := by
  simpa only [triadicHalf_four_mul] using
    (AEGIS.RHOptimizedSchurGlobalJoinV1.actual_mixed_B_norm_time_horizon
      K (4 * d) (by omega) hdK g a hm hw)

/-- The prime-side certificate is invariant under a common translation
of the mother packet. No hypothesis about the absolute lattice origin. -/
theorem actual_prime_four_log_three_signed_cost_at_centers
    (K d : ℕ) (hd : 1 ≤ d) (hdK : 4 * d ≤ K)
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a)
    (u v : ℝ)
    (hgap : v - u = ((4 * d : ℕ) : ℝ) * Real.log 3) :
    (WeilPrimeSumV1 (mixed (translatePacket g u)
      (translatePacket g v))).re ≤
      (1 / 9 : ℝ) ^ d *
        (energy (translatePacket g u).1 +
          energy (translatePacket g v).1) := by
  have hgap' :
      v - u = (((4 * d : ℕ) : ℝ) * Real.log 3) - 0 := by
    simpa using hgap
  have htranslate :=
    AEGIS.WeilTranslationGapInvariantV10.mixed_translate_eq_of_gap_v10
      g u v 0 (((4 * d : ℕ) : ℝ) * Real.log 3) hgap'
  rw [htranslate]
  simpa only [translate_energy] using
    (actual_prime_four_log_three_signed_cost K d hd hdK g a hw)

/-- The actual full complex Weil B bound for any two same-mother
translations with a four-log-three gap. This preserves the full
Archimedean term and does not assert a universal packet selector. -/
theorem actual_mixed_B_norm_at_centers
    (K d : ℕ) (hd : 1 ≤ d) (hdK : 4 * d ≤ K)
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hm : WeilMomentConditionsV1 g)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a)
    (u v : ℝ)
    (hgap : v - u = ((4 * d : ℕ) : ℝ) * Real.log 3) :
    ‖B (translatePacket g u) (translatePacket g v)‖ ≤
      (Real.log 3 * (1 / 9 : ℝ) ^ d + 1 / 100) * energy g.1 := by
  have hgap' :
      v - u = (((4 * d : ℕ) : ℝ) * Real.log 3) - 0 := by
    simpa using hgap
  have htranslate :=
    AEGIS.WeilTranslationGapInvariantV10.B_translate_eq_of_gap_v10
      g u v 0 (((4 * d : ℕ) : ℝ) * Real.log 3) hgap'
  rw [htranslate]
  exact actual_mixed_B_norm_four_log_three K d hd hdK g a hm hw

/-- An arbitrary finite sparse, equally-spaced-gap same-mother family
has a strictly negative real Weil Gram contraction. The actual prime
row is produced internally from the exact von Mangoldt formula, not
assumed. The hypotheses retain the separated family and exact
reconstruction scope; this does not supply a selector for arbitrary g. -/
theorem actual_four_log_three_same_mother_family_sign
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : Fin (n + 1) → ℝ)
    (hwidth : ∀ i,
      AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i))
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hsep : ∀ i j : Fin (n + 1), i < j →
      1 ≤ Nat.dist i j ∧
        (65 / 32 : ℝ) * (Nat.dist i j : ℝ) ≤ center j - center i)
    (K : ℕ) (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a)
    (hfamily : ∀ i, gs i = translatePacket g (center i))
    (hgap : ∀ i j : Fin (n + 1), i < j →
      4 * Nat.dist i j ≤ K ∧
        center j - center i =
          ((4 * Nat.dist i j : ℕ) : ℝ) * Real.log 3) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
      (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
      -(641 / 32768 : ℝ) * (∑ i, energy (gs i).1) := by
  let primeCost : Fin (n + 1) → Fin (n + 1) → ℝ :=
    fun i j => (1 / 9 : ℝ) ^ Nat.dist i j
  have hsym : ∀ i j, primeCost i j = primeCost j i := by
    intro i j
    dsimp [primeCost]
    rw [Nat.dist_comm]
  have hprime : ∀ i j : Fin (n + 1), i < j →
      (WeilPrimeSumV1 (mixed (gs i) (gs j))).re ≤
        primeCost i j * (energy (gs i).1 + energy (gs j).1) := by
    intro i j hij
    obtain ⟨hd, _⟩ := hsep i j hij
    obtain ⟨hdK, hgapij⟩ := hgap i j hij
    have hp := actual_prime_four_log_three_signed_cost_at_centers
      K (Nat.dist i j) hd hdK g a hw
        (center i) (center j) hgapij
    simpa only [primeCost, hfamily i, hfamily j] using hp
  have hrow : ∀ i,
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        primeCost i j) ≤ (57401 / 65536 : ℝ) := by
    intro i
    simpa only [primeCost] using full_four_log_three_prime_row_arch29 i
  exact
    AEGIS.RHArchRow29V1.actual_far_fine_gram_coercive_of_signed_prime_arch29_row
      gs center hwidth hm hsep primeCost hsym hprime hrow




theorem actual_prime_four_log_three_complex_at_centers
    (K d : ℕ) (hd : 1 ≤ d) (hdK : 4 * d ≤ K)
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a)
    (u v : ℝ)
    (hgap : v - u = ((4 * d : ℕ) : ℝ) * Real.log 3) :
    WeilPrimeSumV1 (mixed (translatePacket g u) (translatePacket g v)) =
      ((Real.log 3 * (1 / 9 : ℝ) ^ d * energy g.1 : ℝ) : ℂ) := by
  have hgap' :
      v - u = (((4 * d : ℕ) : ℝ) * Real.log 3) - 0 := by
    simpa using hgap
  have htranslate :=
    AEGIS.WeilTranslationGapInvariantV10.mixed_translate_eq_of_gap_v10
      g u v 0 (((4 * d : ℕ) : ℝ) * Real.log 3) hgap'
  rw [htranslate]
  simpa only [triadicHalf_four_mul] using
    (AEGIS.RHOptimizedSchurGlobalJoinV1.exact_von_mangoldt_time_horizon
      K (4 * d) (by omega) hdK g a hw)

theorem actual_prime_four_log_three_norm_cost_at_centers
    (K d : ℕ) (hd : 1 ≤ d) (hdK : 4 * d ≤ K)
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a)
    (u v : ℝ)
    (hgap : v - u = ((4 * d : ℕ) : ℝ) * Real.log 3) :
    ‖WeilPrimeSumV1 (mixed (translatePacket g u)
      (translatePacket g v))‖ ≤
      (1 / 9 : ℝ) ^ d *
        (energy (translatePacket g u).1 +
          energy (translatePacket g v).1) := by
  have hlog : 0 ≤ Real.log (3 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hpow : 0 ≤ (1 / 9 : ℝ) ^ d := by positivity
  have hE : 0 ≤ energy g.1 := energy_nonnegative g.1
  have hpos : 0 ≤ Real.log 3 * (1 / 9 : ℝ) ^ d * energy g.1 :=
    mul_nonneg (mul_nonneg hlog hpow) hE
  have heq := actual_prime_four_log_three_complex_at_centers
    K d hd hdK g a hw u v hgap
  have hnorm :
      ‖WeilPrimeSumV1 (mixed (translatePacket g u)
        (translatePacket g v))‖ =
        Real.log 3 * (1 / 9 : ℝ) ^ d * energy g.1 := by
    rw [heq]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
  have hcoeff :
      Real.log 3 * ((1 / 9 : ℝ) ^ d * energy g.1) ≤
        2 * ((1 / 9 : ℝ) ^ d * energy g.1) :=
    mul_le_mul_of_nonneg_right
      AEGIS.RHLogThreeSignedPrimeProducerV1.log_three_le_two
      (mul_nonneg hpow hE)
  calc
    ‖WeilPrimeSumV1 (mixed (translatePacket g u)
      (translatePacket g v))‖ =
        Real.log 3 * (1 / 9 : ℝ) ^ d * energy g.1 := hnorm
    _ = Real.log 3 * ((1 / 9 : ℝ) ^ d * energy g.1) := by ring
    _ ≤ 2 * ((1 / 9 : ℝ) ^ d * energy g.1) := hcoeff
    _ = (1 / 9 : ℝ) ^ d *
        (energy (translatePacket g u).1 +
          energy (translatePacket g v).1) := by
      rw [translate_energy, translate_energy]
      ring

theorem actual_four_log_three_prime_norm_family_sign
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : Fin (n + 1) → ℝ)
    (hwidth : ∀ i,
      AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i))
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hsep : ∀ i j : Fin (n + 1), i < j →
      1 ≤ Nat.dist i j ∧
        (65 / 32 : ℝ) * (Nat.dist i j : ℝ) ≤ center j - center i)
    (K : ℕ) (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a)
    (hfamily : ∀ i, gs i = translatePacket g (center i))
    (hgap : ∀ i j : Fin (n + 1), i < j →
      4 * Nat.dist i j ≤ K ∧
        center j - center i =
          ((4 * Nat.dist i j : ℕ) : ℝ) * Real.log 3) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
      (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
      -(641 / 32768 : ℝ) * (∑ i, energy (gs i).1) := by
  let primeCost : Fin (n + 1) → Fin (n + 1) → ℝ :=
    fun i j => (1 / 9 : ℝ) ^ Nat.dist i j
  have hsym : ∀ i j, primeCost i j = primeCost j i := by
    intro i j
    dsimp [primeCost]
    rw [Nat.dist_comm]
  have hprime : ∀ i j : Fin (n + 1), i < j →
      ‖WeilPrimeSumV1 (mixed (gs i) (gs j))‖ ≤
        primeCost i j * (energy (gs i).1 + energy (gs j).1) := by
    intro i j hij
    obtain ⟨hd, _⟩ := hsep i j hij
    obtain ⟨hdK, hgapij⟩ := hgap i j hij
    have hp := actual_prime_four_log_three_norm_cost_at_centers
      K (Nat.dist i j) hd hdK g a hw
        (center i) (center j) hgapij
    simpa only [primeCost, hfamily i, hfamily j] using hp
  have hrow : ∀ i,
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        primeCost i j) ≤ (57401 / 65536 : ℝ) := by
    intro i
    simpa only [primeCost] using full_four_log_three_prime_row_arch29 i
  exact
    AEGIS.RHArchRow29V1.actual_far_fine_gram_coercive_of_arch29_prime_row
      gs center hwidth hm hsep primeCost hsym hprime hrow

/-- The exact prime row 1/4 and Arch row 29/65536 yield the stronger
uniform actual-Weil margin 20829/16384, for the original sparse family. -/
theorem actual_four_log_three_weighted_norm_coercive_sharp
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : Fin (n + 1) → ℝ)
    (hwidth : ∀ i,
      AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i))
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hsep : ∀ i j : Fin (n + 1), i < j →
      1 ≤ Nat.dist i j ∧
        (65 / 32 : ℝ) * (Nat.dist i j : ℝ) ≤ center j - center i)
    (K : ℕ) (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a)
    (hfamily : ∀ i, gs i = translatePacket g (center i))
    (hgap : ∀ i j : Fin (n + 1), i < j →
      4 * Nat.dist i j ≤ K ∧
        center j - center i =
          ((4 * Nat.dist i j : ℕ) : ℝ) * Real.log 3)
    (z : Fin (n + 1) → ℂ) :
    (B (packetSum z gs) (packetSum z gs)).re ≤
      -(20829 / 16384 : ℝ) *
        (∑ i, energy (gs i).1 * ‖z i‖ ^ 2) := by
  let primeCost : Fin (n + 1) → Fin (n + 1) → ℝ :=
    fun i j => (1 / 9 : ℝ) ^ Nat.dist i j
  let archCost : Fin (n + 1) → Fin (n + 1) → ℝ :=
    fun i j => ((1 / 32 : ℝ) * (54 / 53)) *
      ((1 / 145 : ℝ) ^ Nat.dist i j)
  let c : Fin (n + 1) → Fin (n + 1) → ℝ :=
    fun i j => if i = j then 0 else 2 * (primeCost i j + archCost i j)
  let w : Fin (n + 1) → ℝ := fun _ => 1
  have hE : 0 ≤ energy g.1 := energy_nonnegative g.1
  have hweight : ∀ i, 0 < w i := by intro i; norm_num [w]
  have hcpos : ∀ i j, 0 ≤ c i j := by
    intro i j
    dsimp [c, primeCost, archCost]
    split_ifs <;> positivity
  have hcdiag : ∀ i, c i i = 0 := by intro i; simp [c]
  have hcsym : ∀ i j, c i j = c j i := by
    intro i j
    by_cases hij : i = j
    · subst j; rfl
    · have hji : j ≠ i := Ne.symm hij
      simp [c, primeCost, archCost, hij, hji, Nat.dist_comm]
  have hdiag : ∀ i,
      (116142 / 65536 : ℝ) * energy (gs i).1 ≤
        -(B (gs i) (gs i)).re := by
    intro i
    have hfine :=
      AEGIS.RHFineDiagonalUpgradeV3.fine_diagonal_5671_over_3200_v3
        (gs i) (center i) (hwidth i)
    exact (mul_le_mul_of_nonneg_right
      (by norm_num : (116142 / 65536 : ℝ) ≤ 5671 / 3200)
      (energy_nonnegative (gs i).1)).trans hfine
  have hprime : ∀ i j : Fin (n + 1), i < j →
      ‖WeilPrimeSumV1 (mixed (gs i) (gs j))‖ ≤
        primeCost i j * (energy (gs i).1 + energy (gs j).1) := by
    intro i j hij
    obtain ⟨hd, _⟩ := hsep i j hij
    obtain ⟨hdK, hgapij⟩ := hgap i j hij
    have hp := actual_prime_four_log_three_norm_cost_at_centers
      K (Nat.dist i j) hd hdK g a hw
      (center i) (center j) hgapij
    simpa only [primeCost, hfamily i, hfamily j] using hp
  have hforward (i j : Fin (n + 1)) (hij : i < j) :
      ‖B (gs i) (gs j)‖ ≤
        (primeCost i j + archCost i j) *
          (energy (gs i).1 + energy (gs j).1) := by
    obtain ⟨hk, hgapij⟩ := hsep i j hij
    have ha := AEGIS.RHArchRow29V1.actual_B_norm_le_prime_plus_arch145
      (gs i) (gs j) (center i) (center j)
      (hwidth i) (hwidth j) (hm i)
      (Nat.dist i j) hk hgapij
    calc
      ‖B (gs i) (gs j)‖ ≤
          ‖WeilPrimeSumV1 (mixed (gs i) (gs j))‖ +
            archCost i j * (energy (gs i).1 + energy (gs j).1) := by
              simpa only [archCost] using ha
      _ ≤ primeCost i j *
          (energy (gs i).1 + energy (gs j).1) +
          archCost i j * (energy (gs i).1 + energy (gs j).1) :=
            add_le_add (hprime i j hij) le_rfl
      _ = (primeCost i j + archCost i j) *
          (energy (gs i).1 + energy (gs j).1) := by ring
  have hcross : ∀ i j, i ≠ j →
      ‖B (gs i) (gs j)‖ ≤
        c i j * (Real.sqrt (energy (gs i).1) *
          Real.sqrt (energy (gs j).1)) := by
    intro i j hij
    have hi : energy (gs i).1 = energy g.1 := by
      rw [hfamily i, translate_energy]
    have hj : energy (gs j).1 = energy g.1 := by
      rw [hfamily j, translate_energy]
    have hsqrt :
        Real.sqrt (energy (gs i).1) *
          Real.sqrt (energy (gs j).1) = energy g.1 := by
      rw [hi, hj, ← pow_two, Real.sq_sqrt hE]
    have hcost :
        (primeCost i j + archCost i j) *
          (energy (gs i).1 + energy (gs j).1) =
          c i j * (Real.sqrt (energy (gs i).1) *
            Real.sqrt (energy (gs j).1)) := by
      rw [hsqrt, hi, hj]
      simp only [c, if_neg hij]
      ring
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · exact (hforward i j hijlt).trans_eq hcost
    · have hb := hforward j i hjilt
      have hnorm : ‖B (gs i) (gs j)‖ =
          ‖B (gs j) (gs i)‖ := by
        rw [B_hermitian, Complex.norm_conj]
      have hcost_sym :
          primeCost j i + archCost j i =
            primeCost i j + archCost i j := by
        simp [primeCost, archCost, Nat.dist_comm]
      rw [hnorm]
      calc
        ‖B (gs j) (gs i)‖ ≤
            (primeCost j i + archCost j i) *
              (energy (gs j).1 + energy (gs i).1) := hb
        _ = (primeCost i j + archCost i j) *
              (energy (gs i).1 + energy (gs j).1) := by
              rw [hcost_sym]
              ring
        _ = c i j * (Real.sqrt (energy (gs i).1) *
              Real.sqrt (energy (gs j).1)) := hcost
  have hrow (i : Fin (n + 1)) :
      (∑ j, c i j * (w j / w i)) ≤
        (32826 / 65536 : ℝ) := by
    have hprimeRow := full_four_log_three_prime_row i
    have harchRow := AEGIS.RHArchRow29V1.geometric_arch_row_29 i
    have hsum :
        (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) =
          2 * (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
            primeCost i j) +
          2 * (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
            archCost i j) := by
      calc
        (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) =
            ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
              (2 * primeCost i j + 2 * archCost i j) := by
                apply Finset.sum_congr rfl
                intro j hj
                have hij : i ≠ j := by
                  intro heq
                  exact (Finset.mem_erase.mp hj).1 heq.symm
                simp [c, hij]
                ring
        _ = 2 * (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
              primeCost i j) +
            2 * (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
              archCost i j) := by
                rw [Finset.sum_add_distrib]
                simp only [Finset.mul_sum]
    have hrow0 :
        (∑ j, c i j) ≤ (32826 / 65536 : ℝ) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      simp only [hcdiag i, zero_add]
      rw [hsum]
      change (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        archCost i j) ≤ (29 / 65536 : ℝ) at harchRow
      linarith
    simpa [w] using hrow0
  have h := AEGIS.WeightedSchur.weighted_gram_variable_energy
    (fun i j => B (gs i) (gs j)) z
    (fun i => energy (gs i).1) c w
    (116142 / 65536 : ℝ) (32826 / 65536 : ℝ)
    (fun i => energy_nonnegative (gs i).1)
    hcpos hcdiag hcsym hweight hdiag hcross hrow
  have hmargin :
      (116142 / 65536 : ℝ) - 32826 / 65536 = 20829 / 16384 :=
    by norm_num
  rw [hmargin] at h
  rw [B_packetSum]
  exact h


theorem actual_four_log_three_weighted_norm_coercive
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : Fin (n + 1) → ℝ)
    (hwidth : ∀ i,
      AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i))
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hsep : ∀ i j : Fin (n + 1), i < j →
      1 ≤ Nat.dist i j ∧
        (65 / 32 : ℝ) * (Nat.dist i j : ℝ) ≤ center j - center i)
    (K : ℕ) (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a)
    (hfamily : ∀ i, gs i = translatePacket g (center i))
    (hgap : ∀ i j : Fin (n + 1), i < j →
      4 * Nat.dist i j ≤ K ∧
        center j - center i =
          ((4 * Nat.dist i j : ℕ) : ℝ) * Real.log 3)
    (z : Fin (n + 1) → ℂ) :
    (B (packetSum z gs) (packetSum z gs)).re ≤
      -(641 / 32768 : ℝ) *
        (∑ i, energy (gs i).1 * ‖z i‖ ^ 2) := by
  have h := actual_four_log_three_weighted_norm_coercive_sharp
    gs center hwidth hm hsep K g a hw hfamily hgap z
  have henergy : 0 ≤ (∑ i, energy (gs i).1 * ‖z i‖ ^ 2) :=
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (energy_nonnegative (gs i).1) (sq_nonneg _))
  exact h.trans (mul_le_mul_of_nonneg_right
    (by norm_num : -(20829 / 16384 : ℝ) ≤ -(641 / 32768 : ℝ)) henergy)


/-!
## Source-bound signed-real row integration

The prime component is the actual von Mangoldt pairing at four-log-three
gaps. The Arch component is the real-part inequality from RHArchRow29V1.
Unlike a norm-only conversion, no favorable signed mixed term is deleted.

The row coefficient multiplies Eᵢ + Eⱼ, not sqrt(Eᵢ Eⱼ).
Accordingly its contribution to the full Gram is 2R.
-/

theorem actual_four_log_three_source_signed_row_certificate
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : Fin (n + 1) → ℝ)
    (hwidth : ∀ i,
      AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i))
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hsep : ∀ i j : Fin (n + 1), i < j →
      1 ≤ Nat.dist i j ∧
        (65 / 32 : ℝ) * (Nat.dist i j : ℝ) ≤ center j - center i)
    (K : ℕ) (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a)
    (hfamily : ∀ i, gs i = translatePacket g (center i))
    (hgap : ∀ i j : Fin (n + 1), i < j →
      4 * Nat.dist i j ≤ K ∧
        center j - center i =
          ((4 * Nat.dist i j : ℕ) : ℝ) * Real.log 3) :
    ∃ c : Fin (n + 1) → Fin (n + 1) → ℝ,
      (∀ i j, c i j = c j i) ∧
      (∀ i j, i ≠ j →
        (B (gs i) (gs j)).re ≤
          c i j * (energy (gs i).1 + energy (gs j).1)) ∧
      (∀ i, (∑ j ∈
        (Finset.univ : Finset (Fin (n + 1))).erase i,
          c i j) ≤ (16413 / 65536 : ℝ)) := by
  let primeCost : Fin (n + 1) → Fin (n + 1) → ℝ :=
    fun i j => (1 / 9 : ℝ) ^ Nat.dist i j
  let archCost : Fin (n + 1) → Fin (n + 1) → ℝ :=
    fun i j => ((1 / 32 : ℝ) * (54 / 53)) *
      ((1 / 145 : ℝ) ^ Nat.dist i j)
  let c : Fin (n + 1) → Fin (n + 1) → ℝ :=
    fun i j => primeCost i j + archCost i j
  have hsym : ∀ i j, c i j = c j i := by
    intro i j
    dsimp [c, primeCost, archCost]
    simp only [Nat.dist_comm]
  have hprime : ∀ i j : Fin (n + 1), i < j →
      (WeilPrimeSumV1 (mixed (gs i) (gs j))).re ≤
        primeCost i j * (energy (gs i).1 + energy (gs j).1) := by
    intro i j hij
    obtain ⟨hd, _⟩ := hsep i j hij
    obtain ⟨hdK, hgapij⟩ := hgap i j hij
    have hp := actual_prime_four_log_three_signed_cost_at_centers
      K (Nat.dist i j) hd hdK g a hw
      (center i) (center j) hgapij
    simpa only [primeCost, hfamily i, hfamily j] using hp
  have hforward (i j : Fin (n + 1)) (hij : i < j) :
      (B (gs i) (gs j)).re ≤
        c i j * (energy (gs i).1 + energy (gs j).1) := by
    obtain ⟨hk, hgeometric⟩ := hsep i j hij
    have ha := AEGIS.RHArchRow29V1.actual_B_re_le_signed_prime_plus_arch145
      (gs i) (gs j) (center i) (center j)
      (hwidth i) (hwidth j) (hm i)
      (Nat.dist i j) hk hgeometric
    calc
      (B (gs i) (gs j)).re ≤
          (WeilPrimeSumV1 (mixed (gs i) (gs j))).re +
            archCost i j * (energy (gs i).1 + energy (gs j).1) := by
              simpa only [archCost] using ha
      _ ≤ primeCost i j * (energy (gs i).1 + energy (gs j).1) +
            archCost i j * (energy (gs i).1 + energy (gs j).1) :=
          add_le_add (hprime i j hij) le_rfl
      _ = c i j * (energy (gs i).1 + energy (gs j).1) := by
          dsimp [c]
          ring
  have hcross : ∀ i j, i ≠ j →
      (B (gs i) (gs j)).re ≤
        c i j * (energy (gs i).1 + energy (gs j).1) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · exact hforward i j hijlt
    · have hb := hforward j i hjilt
      have hre : (B (gs i) (gs j)).re =
          (B (gs j) (gs i)).re := by
        rw [B_hermitian, Complex.conj_re]
      calc
        (B (gs i) (gs j)).re = (B (gs j) (gs i)).re := hre
        _ ≤ c j i * (energy (gs j).1 + energy (gs i).1) := hb
        _ = c i j * (energy (gs i).1 + energy (gs j).1) := by
            rw [hsym j i, add_comm]
  have hrow : ∀ i, (∑ j ∈
      (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j) ≤ (16413 / 65536 : ℝ) := by
    intro i
    have hp : (∑ j ∈
        (Finset.univ : Finset (Fin (n + 1))).erase i,
          primeCost i j) ≤ (1 / 4 : ℝ) := by
      simpa only [primeCost] using full_four_log_three_prime_row i
    have ha : (∑ j ∈
        (Finset.univ : Finset (Fin (n + 1))).erase i,
          archCost i j) ≤ (29 / 65536 : ℝ) := by
      simpa only [archCost] using AEGIS.RHArchRow29V1.geometric_arch_row_29 i
    calc
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) =
          (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
            primeCost i j) +
          (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
            archCost i j) := by
              simp only [c, Finset.sum_add_distrib]
      _ ≤ (1 / 4 : ℝ) + 29 / 65536 := add_le_add hp ha
      _ = 16413 / 65536 := by norm_num
  exact ⟨c, hsym, hcross, hrow⟩

/-- The source-built signed row connects to the unrestricted-energy
mixed-defect algebra with the exact factor two. The source family still
retains its actual narrow-support and four-log-three gap conditions. -/
theorem actual_four_log_three_signed_gram_sharp
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : Fin (n + 1) → ℝ)
    (hwidth : ∀ i,
      AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i))
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hsep : ∀ i j : Fin (n + 1), i < j →
      1 ≤ Nat.dist i j ∧
        (65 / 32 : ℝ) * (Nat.dist i j : ℝ) ≤ center j - center i)
    (K : ℕ) (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a)
    (hfamily : ∀ i, gs i = translatePacket g (center i))
    (hgap : ∀ i j : Fin (n + 1), i < j →
      4 * Nat.dist i j ≤ K ∧
        center j - center i =
          ((4 * Nat.dist i j : ℕ) : ℝ) * Real.log 3) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
      (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
      -(20829 / 16384 : ℝ) * (∑ i, energy (gs i).1) := by
  obtain ⟨c, hsym, hcross, hrow⟩ :=
    actual_four_log_three_source_signed_row_certificate
      gs center hwidth hm hsep K g a hw hfamily hgap
  have hdiag : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re := by
    intro i
    exact AEGIS.RHFineDiagonalUpgradeV3.fine_diagonal_5671_over_3200_v3
      (gs i) (center i) (hwidth i)
  have hdefect :=
    AEGIS.RHActualUniversalFineGramV1.actual_mixed_defect_le_of_signed_symmetric_row
      gs c (16413 / 65536 : ℝ) hsym hcross hrow
  have hlocal :=
    AEGIS.RHActualUniversalFineGramV1.fine_mixed_defect_lower_bound n gs hdiag
  have hgram :
      (B (packetSum (fun _ => (1 : ℂ)) gs)
         (packetSum (fun _ => (1 : ℂ)) gs)).re =
      (∑ i, ∑ j, B (gs i) (gs j)).re := by
    rw [B_packetSum]
    simp
  rw [← hgram] at hlocal
  have hE : 0 ≤ (∑ i, energy (gs i).1) :=
    Finset.sum_nonneg (fun i _ => energy_nonnegative (gs i).1)
  have hfloor :
      (116142 / 65536 : ℝ) * (∑ i, energy (gs i).1) ≤
        (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1) :=
    mul_le_mul_of_nonneg_right (by norm_num) hE
  linarith [hdefect, hlocal, hfloor]

end AEGIS.RHFourLogThreeActualPrimeV1

#print axioms AEGIS.RHFourLogThreeActualPrimeV1.triadicHalf_four_mul
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.actual_prime_four_log_three_exact
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.actual_prime_four_log_three_signed_cost
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.full_four_log_three_prime_row
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.full_four_log_three_prime_row_arch29
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.actual_mixed_B_norm_four_log_three
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.actual_prime_four_log_three_signed_cost_at_centers
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.actual_mixed_B_norm_at_centers
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.actual_four_log_three_same_mother_family_sign
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.actual_prime_four_log_three_complex_at_centers
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.actual_prime_four_log_three_norm_cost_at_centers
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.actual_four_log_three_prime_norm_family_sign
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.actual_four_log_three_weighted_norm_coercive_sharp
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.actual_four_log_three_weighted_norm_coercive
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.actual_four_log_three_source_signed_row_certificate
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.actual_four_log_three_signed_gram_sharp
