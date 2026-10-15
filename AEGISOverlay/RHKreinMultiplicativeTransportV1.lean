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

import RHLocalKreinPartitionV1
import WeilMixedAlgebraV2
import RHCofinalSchurAdapterV1
import Mathlib.Tactic

/-!
# AEGIS: exact inverse-log transport of the universal Krein partition

Converts the two actual compact Krein atoms obtained for *every* moment-zero
Weil test packet back into genuine multiplicative functions on the positive
half-line. It transports both vanishing moments and reconstructs the original
function exactly, retaining the mixed terms rather than dropping them.

This does NOT yet provide a Schur lower bound.
-/

open Set MeasureTheory
open scoped ContDiff BigOperators Topology
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinMultiplicativeTransportV1

open AEGIS.RHKreinFactorV13
open AEGIS.RHLocalKreinPartitionV1

def unlift (F : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0 < x then (Real.exp (-Real.log x / 2) : ℂ) * F (Real.log x) else 0

theorem lift_unlift (F : ℝ → ℂ) : lift (unlift F) = F := by
  funext t
  have ht : (0 : ℝ) < Real.exp t := Real.exp_pos t
  unfold lift unlift
  rw [if_pos ht, Real.log_exp]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  have hz : t / 2 + -t / 2 = 0 := by ring
  simp [hz]

theorem unlift_lift (g : WeilCompactSmoothGV1) : unlift (lift g.1) = g.1 := by
  funext x
  by_cases hx : 0 < x
  · unfold unlift lift
    rw [if_pos hx, Real.exp_log hx]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    have hz : -Real.log x / 2 + Real.log x / 2 = 0 := by ring
    simp [hz]
  · have hxnot : x ∉ tsupport g.1 := by
      intro hmem
      exact hx (g.2.2.2 hmem)
    have hg : g.1 x = 0 := image_eq_zero_of_notMem_tsupport hxnot
    simp [unlift, hx, hg]

theorem unlift_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℂ) :
    unlift (fun t => ∑ i ∈ s, F i t) =
      fun x => ∑ i ∈ s, unlift (F i) x := by
  funext x
  by_cases hx : 0 < x
  · simp [unlift, hx, Finset.mul_sum]
  · simp [unlift, hx]

theorem unlift_zero_below (F : ℝ → ℂ) (a b : ℝ)
    (hs : tsupport F ⊆ Icc a b) {x : ℝ}
    (hx : x ≤ Real.exp (a - 1)) : unlift F x = 0 := by
  by_cases hxpos : 0 < x
  · have hlog : Real.log x ≤ a - 1 := by
      have h := (Real.log_le_log_iff hxpos (Real.exp_pos _)).2 hx
      simpa only [Real.log_exp] using h
    have hnot : Real.log x ∉ tsupport F := by
      intro hmem
      have hleft := (hs hmem).1
      linarith
    have hzero : F (Real.log x) = 0 := image_eq_zero_of_notMem_tsupport hnot
    simp [unlift, hxpos, hzero]
  · simp [unlift, hxpos]

theorem unlift_zero_above (F : ℝ → ℂ) (a b : ℝ)
    (hs : tsupport F ⊆ Icc a b) {x : ℝ}
    (hx : Real.exp (b + 1) ≤ x) : unlift F x = 0 := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlog : b + 1 ≤ Real.log x := by
    have h := (Real.log_le_log_iff (Real.exp_pos _) hxpos).2 hx
    simpa only [Real.log_exp] using h
  have hnot : Real.log x ∉ tsupport F := by
    intro hmem
    have hright := (hs hmem).2
    linarith
  have hzero : F (Real.log x) = 0 := image_eq_zero_of_notMem_tsupport hnot
  simp [unlift, hxpos, hzero]

theorem unlift_support_interval (F : ℝ → ℂ) (a b : ℝ)
    (hs : tsupport F ⊆ Icc a b) :
    tsupport (unlift F) ⊆ Icc (Real.exp (a - 1)) (Real.exp (b + 1)) := by
  refine closure_minimal ?_ isClosed_Icc
  intro x hx
  by_contra hn
  rcases not_and_or.mp (fun h => hn ⟨h.1, h.2⟩) with h | h
  · exact hx (unlift_zero_below F a b hs (le_of_not_ge h))
  · exact hx (unlift_zero_above F a b hs (le_of_not_ge h))

theorem unlift_hasCompactSupport (F : ℝ → ℂ) (a b : ℝ)
    (hs : tsupport F ⊆ Icc a b) : HasCompactSupport (unlift F) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (unlift_support_interval F a b hs)

theorem unlift_support_positive (F : ℝ → ℂ) (a b : ℝ)
    (hs : tsupport F ⊆ Icc a b) :
    tsupport (unlift F) ⊆ Ioi 0 := by
  intro x hx
  have hleft := (unlift_support_interval F a b hs hx).1
  exact lt_of_lt_of_le (Real.exp_pos _) hleft

theorem unlift_contDiff (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (a b : ℝ) (hs : tsupport F ⊆ Icc a b) :
    ContDiff ℝ ∞ (unlift F) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_or_ge 0 x with hx | hx
  · have hlog : ContDiffAt ℝ ∞ Real.log x :=
      Real.contDiffAt_log.2 (ne_of_gt hx)
    have heReal : ContDiffAt ℝ ∞
        (fun y : ℝ => Real.exp (-Real.log y / 2)) x :=
      Real.contDiff_exp.contDiffAt.comp x (hlog.neg.div_const 2)
    have he : ContDiffAt ℝ ∞
        (fun y : ℝ => (Real.exp (-Real.log y / 2) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x heReal
    have hloc : ContDiffAt ℝ ∞
        (fun y : ℝ => (Real.exp (-Real.log y / 2) : ℂ) * F (Real.log y)) x :=
      he.mul (hF.contDiffAt.comp x hlog)
    have hEq : unlift F =ᶠ[𝓝 x]
        (fun y : ℝ => (Real.exp (-Real.log y / 2) : ℂ) * F (Real.log y)) :=
      by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        have hypos : (0 : ℝ) < y := hy
        simp [unlift, hypos]
    exact ContDiffAt.congr_of_eventuallyEq hloc hEq
  · have hmem : Iio (Real.exp (a - 1)) ∈ 𝓝 x :=
      Iio_mem_nhds (lt_of_le_of_lt hx (Real.exp_pos _))
    have hEq : unlift F =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) :=
      by
        filter_upwards [hmem] with y hy
        exact unlift_zero_below F a b hs (le_of_lt hy)
    exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const hEq

def unliftWeilPacket (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (a b : ℝ) (hs : tsupport F ⊆ Icc a b) : WeilCompactSmoothGV1 :=
  ⟨unlift F, unlift_contDiff F hF a b hs,
    unlift_hasCompactSupport F a b hs,
    unlift_support_positive F a b hs⟩

theorem tsupport_factor_mul (χ φ : ℝ → ℂ) :
    tsupport (fun y => χ y * φ y) ⊆ tsupport φ := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro y hy
  by_contra hnot
  have hzero : φ y = 0 := image_eq_zero_of_notMem_tsupport hnot
  exact hy (by simp [hzero])

theorem unlift_kreinAtom_moments (φ : ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x in Ioi (0 : ℝ), unlift (kreinAtom φ) x / (x : ℂ)) = 0 ∧
    (∫ x in Ioi (0 : ℝ), unlift (kreinAtom φ) x) = 0 := by
  have hm := kreinAtom_moments φ hφ hc
  constructor
  · rw [← lift_moment_minus (unlift (kreinAtom φ)), lift_unlift]
    exact hm.1
  · rw [← lift_moment_plus (unlift (kreinAtom φ)), lift_unlift]
    exact hm.2

theorem unliftWeilPacket_kreinAtom_moments
    (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (a b : ℝ) (hs : tsupport (kreinAtom φ) ⊆ Icc a b)
    (hc : HasCompactSupport φ) :
    WeilMomentConditionsV1
      (unliftWeilPacket (kreinAtom φ) (kreinAtom_contDiff φ hφ) a b hs) := by
  change (∫ x in Ioi (0 : ℝ), unlift (kreinAtom φ) x / (x : ℂ)) = 0 ∧
    (∫ x in Ioi (0 : ℝ), unlift (kreinAtom φ) x) = 0
  exact unlift_kreinAtom_moments φ hφ hc

theorem unlift_add (F H : ℝ → ℂ) :
    unlift (fun t => F t + H t) =
      fun x => unlift F x + unlift H x := by
  funext x
  by_cases hx : 0 < x
  · simp [unlift, hx, mul_add]
  · simp [unlift, hx]

theorem every_moment_zero_packet_two_actual_weil_packets
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) :
    ∃ u v : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 u ∧ WeilMomentConditionsV1 v ∧
      g = AEGIS.WeilMixedAlgebraV2.addPacket u v := by
  obtain ⟨L, hL, hwindow⟩ :=
    AEGIS.WeilWindowExhaustionV1.logLift_has_finite_window_v1 g
  have hs : tsupport (lift g.1) ⊆ Icc (-L) L := hwindow
  obtain ⟨φ, hφ, hsφ, hfactor⟩ :=
    actual_packet_has_supported_krein_factor g hm (-L) L (by linarith) hs
  let ψ₁ : ℝ → ℂ := fun y => χ y * φ y
  let ψ₂ : ℝ → ℂ := fun y => (1 - χ y) * φ y
  have hψ₁ : ContDiff ℝ ∞ ψ₁ := hχ.mul hφ
  have hψ₂ : ContDiff ℝ ∞ ψ₂ := (contDiff_const.sub hχ).mul hφ
  have hcφ : HasCompactSupport φ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsφ
  have hcψ₁ : HasCompactSupport ψ₁ := hcφ.mul_left
  have hcψ₂ : HasCompactSupport ψ₂ := hcφ.mul_left
  have hs₁ : tsupport (kreinAtom ψ₁) ⊆ Icc (-L) L :=
    (kreinAtom_support ψ₁).trans ((tsupport_factor_mul χ φ).trans hsφ)
  have hs₂ : tsupport (kreinAtom ψ₂) ⊆ Icc (-L) L :=
    (kreinAtom_support ψ₂).trans
      ((tsupport_factor_mul (fun y => 1 - χ y) φ).trans hsφ)
  let u : WeilCompactSmoothGV1 :=
    unliftWeilPacket (kreinAtom ψ₁) (kreinAtom_contDiff ψ₁ hψ₁) (-L) L hs₁
  let v : WeilCompactSmoothGV1 :=
    unliftWeilPacket (kreinAtom ψ₂) (kreinAtom_contDiff ψ₂ hψ₂) (-L) L hs₂
  have hu : WeilMomentConditionsV1 u :=
    unliftWeilPacket_kreinAtom_moments ψ₁ hψ₁ (-L) L hs₁ hcψ₁
  have hv : WeilMomentConditionsV1 v :=
    unliftWeilPacket_kreinAtom_moments ψ₂ hψ₂ (-L) L hs₂ hcψ₂
  refine ⟨u, v, hu, hv, ?_⟩
  apply Subtype.ext
  have hsplit : lift g.1 = (fun t => kreinAtom ψ₁ t + kreinAtom ψ₂ t) := by
    rw [hfactor]
    exact (kreinAtom_partition_two φ χ hφ hχ).symm
  have hraw : g.1 = (fun x => unlift (kreinAtom ψ₁) x + unlift (kreinAtom ψ₂) x) := by
    calc
      g.1 = unlift (lift g.1) := (unlift_lift g).symm
      _ = unlift (fun t => kreinAtom ψ₁ t + kreinAtom ψ₂ t) :=
        congrArg unlift hsplit
      _ = (fun x => unlift (kreinAtom ψ₁) x + unlift (kreinAtom ψ₂) x) :=
        unlift_add _ _
  exact hraw

theorem every_packet_actual_two_block_zero_quadratic
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) :
    ∃ u v : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 u ∧ WeilMomentConditionsV1 v ∧
      g = AEGIS.WeilMixedAlgebraV2.addPacket u v ∧
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re =
        -(AEGIS.WeilMixedAlgebraV2.B u u).re +
        2 * (-(AEGIS.WeilMixedAlgebraV2.B u v).re) +
        -(AEGIS.WeilMixedAlgebraV2.B v v).re := by
  obtain ⟨u, v, hu, hv, hsum⟩ :=
    every_moment_zero_packet_two_actual_weil_packets g hm χ hχ
  refine ⟨u, v, hu, hv, hsum, ?_⟩
  rw [hsum] at hm ⊢
  exact AEGIS.RHCofinalSchurAdapterV1.actual_two_block_zero_quadratic_coefficients
    u v hm

theorem every_moment_zero_packet_multiplicative_two_atom
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) :
    ∃ φ : ℝ → ℂ,
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      g.1 = (fun x =>
        unlift (kreinAtom (fun y => χ y * φ y)) x +
        unlift (kreinAtom (fun y => (1 - χ y) * φ y)) x) ∧
      ((∫ x in Ioi (0 : ℝ),
         unlift (kreinAtom (fun y => χ y * φ y)) x / (x : ℂ)) = 0 ∧
       (∫ x in Ioi (0 : ℝ),
         unlift (kreinAtom (fun y => χ y * φ y)) x) = 0) ∧
      ((∫ x in Ioi (0 : ℝ),
         unlift (kreinAtom (fun y => (1 - χ y) * φ y)) x / (x : ℂ)) = 0 ∧
       (∫ x in Ioi (0 : ℝ),
         unlift (kreinAtom (fun y => (1 - χ y) * φ y)) x) = 0) := by
  obtain ⟨φ, hφ, hc, hsplit, hc1, hc2, _hm1, _hm2⟩ :=
    every_moment_zero_packet_two_atom_partition g hm χ hχ
  refine ⟨φ, hφ, hc, ?_, ?_, ?_⟩
  · calc
      g.1 = unlift (lift g.1) := (unlift_lift g).symm
      _ = unlift (fun x =>
            kreinAtom (fun y => χ y * φ y) x +
            kreinAtom (fun y => (1 - χ y) * φ y) x) :=
              congrArg unlift hsplit
      _ = (fun x =>
            unlift (kreinAtom (fun y => χ y * φ y)) x +
            unlift (kreinAtom (fun y => (1 - χ y) * φ y)) x) := by
              funext x
              by_cases hx : 0 < x
              · simp [unlift, hx, mul_add]
              · simp [unlift, hx]
  · exact unlift_kreinAtom_moments _ (hχ.mul hφ) hc1
  · exact unlift_kreinAtom_moments _ ((contDiff_const.sub hχ).mul hφ) hc2


/-- The existing *arbitrary finite* Krein partition is transported to an actual
finite family of smooth, positive-support Weil test packets, with BOTH moments
zero and exact reconstruction. No positivity or mixed-term estimate is assumed.

This is the source-level bridge from the universal log-coordinate partition
to the finite actual-Weil Gram carrier. -/
theorem every_moment_zero_packet_finite_actual_weil_partition
    {ι : Type*} (s : Finset ι)
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (χ : ι → ℝ → ℂ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hpart : ∀ x : ℝ, ∑ i ∈ s, χ i x = 1) :
    ∃ gs : ι → WeilCompactSmoothGV1,
      (∀ i ∈ s, WeilMomentConditionsV1 (gs i)) ∧
      g.1 = (fun x => ∑ i ∈ s, (gs i).1 x) := by
  classical
  obtain ⟨L, hL, hwindow⟩ :=
    AEGIS.WeilWindowExhaustionV1.logLift_has_finite_window_v1 g
  have hs : tsupport (lift g.1) ⊆ Icc (-L) L := hwindow
  obtain ⟨φ, hφ, hsφ, hsplit, _hlocal⟩ :=
    actual_packet_finite_krein_decomposition s g hm (-L) L
      (by linarith) hs χ hχ (by
        intro x _
        exact hpart x)
  let ψ (i : ι) : ℝ → ℂ := fun y => χ i y * φ y
  have hψ (i : ι) : ContDiff ℝ ∞ (ψ i) := (hχ i).mul hφ
  have hψsupp (i : ι) :
      tsupport (kreinAtom (ψ i)) ⊆ Icc (-L) L :=
    (kreinAtom_support (ψ i)).trans
      ((tsupport_factor_mul (χ i) φ).trans hsφ)
  have hcφ : HasCompactSupport φ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsφ
  have hcψ (i : ι) : HasCompactSupport (ψ i) := hcφ.mul_left
  let gs (i : ι) : WeilCompactSmoothGV1 :=
    unliftWeilPacket (kreinAtom (ψ i))
      (kreinAtom_contDiff (ψ i) (hψ i)) (-L) L (hψsupp i)
  refine ⟨gs, ?_, ?_⟩
  · intro i _
    exact unliftWeilPacket_kreinAtom_moments
      (ψ i) (hψ i) (-L) L (hψsupp i) (hcψ i)
  · have hsplit' :
        lift g.1 = (fun x => ∑ i ∈ s, kreinAtom (ψ i) x) := hsplit
    calc
      g.1 = unlift (lift g.1) := (unlift_lift g).symm
      _ = unlift (fun x => ∑ i ∈ s, kreinAtom (ψ i) x) :=
        congrArg unlift hsplit'
      _ = (fun x => ∑ i ∈ s, unlift (kreinAtom (ψ i)) x) :=
        unlift_finset_sum s (fun i => kreinAtom (ψ i))
      _ = (fun x => ∑ i ∈ s, (gs i).1 x) := rfl

end AEGIS.RHKreinMultiplicativeTransportV1

#print axioms AEGIS.RHKreinMultiplicativeTransportV1.lift_unlift
#print axioms AEGIS.RHKreinMultiplicativeTransportV1.unlift_lift
#print axioms AEGIS.RHKreinMultiplicativeTransportV1.unlift_contDiff
#print axioms AEGIS.RHKreinMultiplicativeTransportV1.every_moment_zero_packet_two_actual_weil_packets
#print axioms AEGIS.RHKreinMultiplicativeTransportV1.every_packet_actual_two_block_zero_quadratic
#print axioms AEGIS.RHKreinMultiplicativeTransportV1.unlift_finset_sum
#print axioms AEGIS.RHKreinMultiplicativeTransportV1.unlift_kreinAtom_moments
#print axioms AEGIS.RHKreinMultiplicativeTransportV1.every_moment_zero_packet_multiplicative_two_atom

#print axioms AEGIS.RHKreinMultiplicativeTransportV1.every_moment_zero_packet_finite_actual_weil_partition
