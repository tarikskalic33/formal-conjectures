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

import AEGISOverlay.RHTargetPacketMellinGeneralV2
import AEGISOverlay.RHCompactMellinEntireV1
import AEGISOverlay.RHDetectingPacketV1
import AEGISOverlay.RHGenericSpectralShiftV1
import RestrictedWeilCriterionResidueCoefficientV11
import WeilZeroTwoPointV11
import AEGISOverlay.RHDetectingPacketCriterionV1
import AEGISOverlay.RHFixedPacketFourPhaseV1
import WeilWindowExhaustionV1
import RHThreeCellClassV13

/-!
# One fixed *narrow* detecting packet

The source-exact TargetPacketV11 family has moments zero and x-support
within exp(±1/32) for every complex parameter. The already kernel-replayed
general Mellin identity, entire-Mellin lemma, generic real shift, and the
countable bad-ratio argument yield a single narrow packet whose zero-kernel
coefficients detect every nontrivial zeta zero.

This proves no global translated sign, kernel bound, or RH statement.
-/

set_option autoImplicit false
noncomputable section

open Set Complex
open scoped ComplexConjugate

namespace AEGIS.RHNarrowFixedDetectorV1

open AEGIS.RestrictedWeilCriterionResidueWitnessV11
open AEGIS.RestrictedWeilCriterionResidueCoefficientV11
open AEGIS.RHTargetPacketMellinGeneralV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilZeroTwoPointV11
open AEGIS.WeilZeroTranslationV11
open AEGIS.RestrictedWeilCriterionKernelBridgeV10

private def narrowWindow : Set ℝ :=
  Icc (Real.exp (-(1 / 32 : ℝ))) (Real.exp (1 / 32 : ℝ))

private theorem targetPacket_narrowWindow (alpha : ℂ) :
    tsupport (TargetPacketV11 alpha).1 ⊆ narrowWindow := by
  simpa only [narrowWindow, TargetPacketV11] using
    targetPacketFun_tsupport_subset_v11 alpha

/-- Two explicitly parametrized target packets have no common Mellin zero
in the critical strip; the parameter choice does not enlarge support. -/
theorem exists_narrow_complementary_pair :
    ∃ p q : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 p ∧ WeilMomentConditionsV1 q ∧
      tsupport p.1 ⊆ narrowWindow ∧
      tsupport q.1 ⊆ narrowWindow ∧
      ∀ s : ℂ, 0 < s.re → s.re < 1 →
        ¬ (mellin p.1 s = 0 ∧ mellin q.1 s = 0) := by
  let p := TargetPacketV11 (2 : ℂ)
  have hpNonzero : mellin p.1 (2 : ℂ) ≠ 0 := by
    simpa only [p] using targetPacket_mellin_target_ne_zero_v11
      (2 : ℂ) (by norm_num) (by norm_num)
  obtain ⟨a, ha⟩ :=
    AEGIS.RHGenericSpectralShiftV1.exists_real_shift_no_common_zero_of_entire
      (mellin p.1) (AEGIS.RHCompactMellinEntireV1.packet_mellin_entire p)
      (2 : ℂ) hpNonzero
  let q := TargetPacketV11 (2 - (a : ℂ))
  refine ⟨p, q, targetPacket_moments_v11 _, targetPacket_moments_v11 _,
    targetPacket_narrowWindow _, targetPacket_narrowWindow _, ?_⟩
  intro s hslo hshi ⟨hpzero, hqzero⟩
  apply ha s
  refine ⟨hpzero, ?_⟩
  have hs0 : s ≠ 0 := by
    intro h
    have hr : s.re = 0 := by simpa using congrArg Complex.re h
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hr : s.re = 1 := by simpa using congrArg Complex.re h
    linarith
  have hQformula :
      mellin q.1 s =
        s * (s - 1) * seedMellinV2 (s - (2 - (a : ℂ))) := by
    simpa only [q] using targetPacket_mellin_general_v2 (2 - (a : ℂ)) s
  rw [hQformula] at hqzero
  have hprod :
      (s * (s - 1)) * seedMellinV2 (s - (2 - (a : ℂ))) = 0 := by
    simpa only [mul_assoc] using hqzero
  have hseed : seedMellinV2 (s - (2 - (a : ℂ))) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left
      (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))
  change mellin (TargetPacketV11 (2 : ℂ)).1 (s + (a : ℂ)) = 0
  rw [targetPacket_mellin_general_v2]
  have harg : (s + (a : ℂ)) - 2 = s - (2 - (a : ℂ)) := by ring
  rw [harg, hseed]
  simp

/-- Exact support control survives the countable bad-ratio linear combination. -/
theorem exists_narrow_mellin_detecting_packet :
    ∃ g : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 g ∧
      tsupport g.1 ⊆ narrowWindow ∧
      ∀ rho : RiemannNontrivialZeroIndexV2,
        mellin g.1 rho.1 ≠ 0 ∧
        mellin g.1 (1 - conj rho.1) ≠ 0 := by
  obtain ⟨p, q, hp, hq, hpsupp, hqsupp, hpair⟩ :=
    exists_narrow_complementary_pair
  let bad₁ : Set ℝ := Set.range (fun rho : RiemannNontrivialZeroIndexV2 =>
    (-mellin p.1 rho.1 / mellin q.1 rho.1).re)
  let bad₂ : Set ℝ := Set.range (fun rho : RiemannNontrivialZeroIndexV2 =>
    (-mellin p.1 (1 - conj rho.1) /
      mellin q.1 (1 - conj rho.1)).re)
  have hc₁ : bad₁.Countable := Set.countable_range _
  have hc₂ : bad₂.Countable := Set.countable_range _
  have hex : ∃ b : ℝ, b ∉ bad₁ ∪ bad₂ := by
    by_contra h
    push Not at h
    have heq : bad₁ ∪ bad₂ = Set.univ := Set.eq_univ_of_forall h
    exact Set.not_countable_univ (heq ▸ hc₁.union hc₂)
  obtain ⟨b, hb⟩ := hex
  let g := addPacket p (scalePacket (b : ℂ) q)
  have hmoment : WeilMomentConditionsV1 g :=
    addPacket_preserves_moments_v10 p (scalePacket (b : ℂ) q) hp
      (scalePacket_preserves_moments_v10 (b : ℂ) q hq)
  have hsupport : tsupport g.1 ⊆ narrowWindow := by
    intro x hx
    change x ∈ tsupport (addPacket p (scalePacket (b : ℂ) q)).1 at hx
    rcases sum_support p (scalePacket (b : ℂ) q) hx with hx | hx
    · exact hpsupp hx
    · exact hqsupp (scale_support (b : ℂ) q hx)
  refine ⟨g, hmoment, hsupport, ?_⟩
  intro rho
  have hstrip := riemann_zeta_nontrivial_zero_critical_strip_v1 rho.2.1 rho.2.2
  have hs₀ : 0 < (1 - conj rho.1).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith [hstrip.2]
  have hs₁ : (1 - conj rho.1).re < 1 := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith [hstrip.1]
  have hr₁ : b ≠ (-mellin p.1 rho.1 / mellin q.1 rho.1).re := by
    intro heq
    exact hb (Or.inl ⟨rho, heq.symm⟩)
  have hr₂ : b ≠
      (-mellin p.1 (1 - conj rho.1) / mellin q.1 (1 - conj rho.1)).re := by
    intro heq
    exact hb (Or.inr ⟨rho, heq.symm⟩)
  change mellin (addPacket p (scalePacket (b : ℂ) q)).1 rho.1 ≠ 0 ∧
    mellin (addPacket p (scalePacket (b : ℂ) q)).1
      (1 - conj rho.1) ≠ 0
  rw [mellin_addPacket_v11, mellin_scalePacket_v11,
    mellin_addPacket_v11, mellin_scalePacket_v11]
  constructor
  · exact AEGIS.RHDetectingPacketV1.affine_ne_zero_of_ratio_excluded _ _ b
      (hpair rho.1 hstrip.1 hstrip.2) hr₁
  · exact AEGIS.RHDetectingPacketV1.affine_ne_zero_of_ratio_excluded _ _ b
      (hpair (1 - conj rho.1) hs₀ hs₁) hr₂

/-- A single genuinely narrow compact smooth packet detects every actual
nontrivial-zero translation coefficient. -/
theorem exists_narrow_fixed_detecting_packet :
    ∃ g : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 g ∧
      tsupport g.1 ⊆ narrowWindow ∧
      ∀ rho : RiemannNontrivialZeroIndexV2,
        WeilZeroCoefficientV11 g rho ≠ 0 := by
  obtain ⟨g, hm, hsupp, hmel⟩ := exists_narrow_mellin_detecting_packet
  refine ⟨g, hm, hsupp, fun rho => ?_⟩
  unfold WeilZeroCoefficientV11
  rw [autocorrelation_zero_summand_factorization_v11]
  have hmult : (analyticOrderNatAt riemannZeta rho.1 : ℂ) ≠ 0 := by
    exact_mod_cast zeta_analyticOrderNatAt_ne_zero_v11 rho
  exact mul_ne_zero hmult
    (mul_ne_zero (hmel rho).1 ((map_ne_zero conj).mpr (hmel rho).2))


/-- A fixed choice of the kernel-verified narrow detector for downstream RH
    estimates. All following facts refer to this exact same packet. -/
def narrowDetectingPacket : WeilCompactSmoothGV1 :=
  Classical.choose exists_narrow_fixed_detecting_packet

theorem narrowDetectingPacket_moments :
    WeilMomentConditionsV1 narrowDetectingPacket :=
  (Classical.choose_spec exists_narrow_fixed_detecting_packet).1

/-- Public support interface, with no inaccessible private window name. -/
theorem narrowDetectingPacket_support :
    tsupport narrowDetectingPacket.1 ⊆
      Icc (Real.exp (-(1 / 32 : ℝ))) (Real.exp (1 / 32 : ℝ)) :=
  (Classical.choose_spec exists_narrow_fixed_detecting_packet).2.1

theorem narrowDetectingPacket_detects (rho : RiemannNontrivialZeroIndexV2) :
    WeilZeroCoefficientV11 narrowDetectingPacket rho ≠ 0 :=
  (Classical.choose_spec exists_narrow_fixed_detecting_packet).2.2 rho


/-- Transport the narrow multiplicative support to the *actual* repository
    logarithmic window predicate, for the same fixed detecting packet. -/
theorem narrowDetectingPacket_logWindow :
    AEGIS.WeilWindowExhaustionV1.LogWindowContainsV1
      narrowDetectingPacket (1 / 32 : ℝ) := by
  intro t ht
  obtain ⟨x, hx, hxt⟩ :=
    AEGIS.WeilWindowExhaustionV1.logLift_tsupport_subset_envelope_v1
      narrowDetectingPacket ht
  have hwindow := narrowDetectingPacket_support hx
  have hxpos : 0 < x := narrowDetectingPacket.2.2.2 hx
  have hlow : -(1 / 32 : ℝ) ≤ Real.log x := by
    have h :=
      (Real.log_le_log_iff (Real.exp_pos (-(1 / 32 : ℝ))) hxpos).2
        hwindow.1
    simpa using h
  have hhigh : Real.log x ≤ (1 / 32 : ℝ) := by
    have h :=
      (Real.log_le_log_iff hxpos (Real.exp_pos (1 / 32 : ℝ))).2
        hwindow.2
    simpa using h
  rw [← hxt]
  exact ⟨hlow, hhigh⟩

/-- An unconditional *actual arithmetic* sign for the fixed narrow detector,
    reusing the existing certified 7/32 three-cell coercivity theorem. -/
theorem narrowDetectingPacket_arithmetic_nonpositive :
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1 narrowDetectingPacket)).re ≤ 0 := by
  have hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      narrowDetectingPacket (7 / 32 : ℝ) 0 := by
    change AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
      narrowDetectingPacket (0 - (7 / 32 : ℝ)) (0 + (7 / 32 : ℝ))
    intro t ht
    have hn := narrowDetectingPacket_logWindow ht
    exact ⟨by linarith [hn.1], by linarith [hn.2]⟩
  have hc := AEGIS.RHThreeCellClassV13.cell_coercive
    narrowDetectingPacket 0 hw narrowDetectingPacket_moments
  have he := AEGIS.WeilDisjointEnergyV2.energy_nonnegative
    narrowDetectingPacket.1
  linarith

/-- For every coefficient c and every shift |d| ≤ 3/16, the actual
    two-point packet fits the already-certified 7/32 logarithmic window. -/
theorem narrowDetectingPacket_local_twoPoint_window
    (d : ℝ) (hd : |d| ≤ (3 / 16 : ℝ)) (c : ℂ) :
    AEGIS.WeilWindowExhaustionV1.LogWindowContainsV1
      (WeilTwoPointTranslateV11 narrowDetectingPacket d c) (7 / 32 : ℝ) := by
  let g := narrowDetectingPacket
  have hdlo := (abs_le.mp hd).1
  have hdhi := (abs_le.mp hd).2
  have hg : AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
      g (-(1 / 32 : ℝ)) (1 / 32 : ℝ) :=
    narrowDetectingPacket_logWindow
  have hleft : AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
      g (-(7 / 32 : ℝ)) (7 / 32 : ℝ) := by
    intro t ht
    have h := hg ht
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have htrans := AEGIS.WeilThreeBlockTranslatedPacketsV22.translate_logSupportIn
    g d (-(1 / 32 : ℝ)) (1 / 32 : ℝ) hg
  have hright : AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
      (AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket g d)
      (-(7 / 32 : ℝ)) (7 / 32 : ℝ) := by
    intro t ht
    have h := htrans ht
    exact ⟨by linarith [h.1, hdlo], by linarith [h.2, hdhi]⟩
  change AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
    (WeilTwoPointTranslateV11 g d c) (-(7 / 32 : ℝ)) (7 / 32 : ℝ)
  unfold AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
  apply closure_minimal ?_ isClosed_Icc
  intro t ht
  by_contra houtside
  have hfirst : AEGIS.WeilLogCoordinateIsometryV21.logLift g.1 t = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hs => houtside (hleft hs))
  have hsecond :
      AEGIS.WeilLogCoordinateIsometryV21.logLift
        (AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket g d).1 t = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hs => houtside (hright hs))
  have heq :
      AEGIS.WeilLogCoordinateIsometryV21.logLift
        (WeilTwoPointTranslateV11 g d c).1 t =
        AEGIS.WeilLogCoordinateIsometryV21.logLift g.1 t +
        c * AEGIS.WeilLogCoordinateIsometryV21.logLift
          (AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket g d).1 t := by
    change ((Real.exp (t / 2) : ℂ) *
        (g.1 (Real.exp t) +
          c * (AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket g d).1
            (Real.exp t))) =
      ((Real.exp (t / 2) : ℂ) * g.1 (Real.exp t)) +
        c * ((Real.exp (t / 2) : ℂ) *
          (AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket g d).1
            (Real.exp t))
    ring
  apply ht
  rw [heq, hfirst, hsecond]
  ring

/-- Certified arithmetic sign for every complex two-point coefficient in the
    complete real translation interval [-3/16, 3/16]. -/
theorem narrowDetectingPacket_local_twoPoint_sign
    (d : ℝ) (hd : |d| ≤ (3 / 16 : ℝ)) (c : ℂ) :
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1
        (WeilTwoPointTranslateV11 narrowDetectingPacket d c))).re ≤ 0 := by
  have hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (WeilTwoPointTranslateV11 narrowDetectingPacket d c) (7 / 32 : ℝ) 0 := by
    simpa only [AEGIS.RHDyadicDiagonalV13.HalfWidthAt,
      AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn,
      AEGIS.WeilWindowExhaustionV1.LogWindowContainsV1,
      zero_sub, zero_add] using narrowDetectingPacket_local_twoPoint_window d hd c
  have hm := AEGIS.WeilZeroKernelHermitianV11.twoPointTranslate_preserves_moments_v11
    narrowDetectingPacket d c narrowDetectingPacket_moments
  have hc := AEGIS.RHThreeCellClassV13.cell_coercive
    (WeilTwoPointTranslateV11 narrowDetectingPacket d c) 0 hw hm
  have he := AEGIS.WeilDisjointEnergyV2.energy_nonnegative
    (WeilTwoPointTranslateV11 narrowDetectingPacket d c).1
  linarith

/-- The real, canonical zero quadratic is nonnegative for every
    two-point packet within the certified shift interval, with arbitrary c. -/
theorem narrowDetectingPacket_local_zero_quadratic_nonnegative
    (d : ℝ) (hd : |d| ≤ (3 / 16 : ℝ)) (c : ℂ) :
    0 ≤ (WeilAutocorrelationZeroQuadraticV11
      (WeilTwoPointTranslateV11 narrowDetectingPacket d c)).re := by
  have hm :=
    AEGIS.WeilZeroKernelHermitianV11.twoPointTranslate_preserves_moments_v11
      narrowDetectingPacket d c narrowDetectingPacket_moments
  exact
    (AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
      (WeilTwoPointTranslateV11 narrowDetectingPacket d c) hm).mp
        (narrowDetectingPacket_local_twoPoint_sign d hd c)

/-- Separate sharp component-wise bounds for the actual zero kernel, with
    the same real diagonal in all four Hermitian phase tests. -/
theorem narrowDetectingPacket_local_kernel_components
    (d : ℝ) (hd : |d| ≤ (3 / 16 : ℝ)) :
    |(WeilZeroTranslationKernelV11 narrowDetectingPacket d).re| ≤
      (WeilAutocorrelationZeroQuadraticV11 narrowDetectingPacket).re ∧
    |(WeilZeroTranslationKernelV11 narrowDetectingPacket d).im| ≤
      (WeilAutocorrelationZeroQuadraticV11 narrowDetectingPacket).re := by
  apply weil_four_phase_nonnegative_components_v1
  intro c _hc
  rw [← AEGIS.RHFixedPacketFourPhaseV1.twoPoint_zero_quadratic_re_eq_four_phase_value
    narrowDetectingPacket narrowDetectingPacket_moments d c]
  exact narrowDetectingPacket_local_zero_quadratic_nonnegative d hd c

/-- Exact uniform bound on the genuine zero translation kernel for all
    shifts in the certified local interval. The constant is the same scalar
    diagonal used by the global fixed-four-phase criterion. -/
theorem narrowDetectingPacket_local_kernel_norm_bound (d : ℝ)
    (hd : |d| ≤ (3 / 16 : ℝ)) :
    ‖WeilZeroTranslationKernelV11 narrowDetectingPacket d‖ ≤
      2 * (WeilAutocorrelationZeroQuadraticV11 narrowDetectingPacket).re := by
  apply weil_four_phase_nonnegative_norm_bound_v1
  intro c _hc
  rw [← AEGIS.RHFixedPacketFourPhaseV1.twoPoint_zero_quadratic_re_eq_four_phase_value
    narrowDetectingPacket narrowDetectingPacket_moments d c]
  have hm :=
    AEGIS.WeilZeroKernelHermitianV11.twoPointTranslate_preserves_moments_v11
      narrowDetectingPacket d c narrowDetectingPacket_moments
  exact
    (AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
      (WeilTwoPointTranslateV11 narrowDetectingPacket d c) hm).mp
        (narrowDetectingPacket_local_twoPoint_sign d hd c)

/-- The existing pole criterion applies to the SAME narrow packet.
    The kernel-bound hypothesis refers to narrowDetectingPacket itself. -/
theorem riemannHypothesis_of_narrow_kernel_bound
    (h : AEGIS.RHDetectingPacketCriterionV1.PacketKernelBoundV1
      narrowDetectingPacket) : RiemannHypothesis :=
  AEGIS.RHDetectingPacketCriterionV1.riemannHypothesis_of_detecting_bounded_kernel
    narrowDetectingPacket narrowDetectingPacket_detects h

/-- Four-phase arithmetic signs for the narrow packet imply the exact Mathlib RH.
    Support and detecting properties are unconditional source theorems. -/
theorem riemannHypothesis_of_narrow_four_phase_sign
    (h : AEGIS.RHFixedPacketFourPhaseV1.FixedPacketFourPhaseSignV1
      narrowDetectingPacket) : RiemannHypothesis :=
  riemannHypothesis_of_narrow_kernel_bound
    (AEGIS.RHFixedPacketFourPhaseV1.fixed_packet_four_phase_implies_bounded_zero_kernel
      narrowDetectingPacket narrowDetectingPacket_moments h)

end AEGIS.RHNarrowFixedDetectorV1

#print axioms AEGIS.RHNarrowFixedDetectorV1.exists_narrow_complementary_pair
#print axioms AEGIS.RHNarrowFixedDetectorV1.exists_narrow_mellin_detecting_packet
#print axioms AEGIS.RHNarrowFixedDetectorV1.exists_narrow_fixed_detecting_packet
#print axioms AEGIS.RHNarrowFixedDetectorV1.narrowDetectingPacket_moments
#print axioms AEGIS.RHNarrowFixedDetectorV1.narrowDetectingPacket_support
#print axioms AEGIS.RHNarrowFixedDetectorV1.narrowDetectingPacket_detects
#print axioms AEGIS.RHNarrowFixedDetectorV1.narrowDetectingPacket_logWindow
#print axioms AEGIS.RHNarrowFixedDetectorV1.narrowDetectingPacket_arithmetic_nonpositive
#print axioms AEGIS.RHNarrowFixedDetectorV1.narrowDetectingPacket_local_twoPoint_window
#print axioms AEGIS.RHNarrowFixedDetectorV1.narrowDetectingPacket_local_twoPoint_sign
#print axioms AEGIS.RHNarrowFixedDetectorV1.narrowDetectingPacket_local_kernel_norm_bound
#print axioms AEGIS.RHNarrowFixedDetectorV1.narrowDetectingPacket_local_zero_quadratic_nonnegative
#print axioms AEGIS.RHNarrowFixedDetectorV1.narrowDetectingPacket_local_kernel_components
#print axioms AEGIS.RHNarrowFixedDetectorV1.riemannHypothesis_of_narrow_kernel_bound
#print axioms AEGIS.RHNarrowFixedDetectorV1.riemannHypothesis_of_narrow_four_phase_sign
