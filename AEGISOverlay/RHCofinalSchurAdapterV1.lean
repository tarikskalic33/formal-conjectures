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

import RHCofinalActualTerminalV1
import RHGramExpansionV13

/-!
# Existing Feshbach/Schur families -> archived cofinal moment-decay terminal

Converts the actual finite mixed quadratic and Schur lower bounds from
RHFeshbachWeilClosureV2 into the exact SAME-sequence cofinal certificate
consumed by RHMomentDecayCofinalJoinV1. No new abstract form or axioms.
The universal family producer is a named premise, never asserted.
-/

open Filter Topology

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHCofinalSchurAdapterV1

open AEGIS.RHFeshbachWeilClosureV2
open AEGIS.RHCofinalActualTerminalV1

/-- A real packet-indexed Schur family with convergent norms supplies the
exact cofinal lower certificate consumed by the verified moment-decay join. -/
theorem cofinal_certificate_of_packet_schur
    (g : WeilCompactSmoothGV1)
    (h : PacketSchurFamily g)
    (normSqLimit : ℝ)
    (hnorm : Tendsto h.normSq atTop (𝓝 normSqLimit)) :
    ∃ (N : ℕ → ℕ) (q normSq : ℕ → ℝ) (limit : ℝ),
      Tendsto N atTop atTop ∧
      Tendsto q atTop
        (𝓝 ((∑' rho : RiemannNontrivialZeroIndexV2,
          WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re)) ∧
      Tendsto normSq atTop (𝓝 limit) ∧
      (∀ j : ℕ,
        -(FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 (N j)) *
          normSq j ≤ q j) := by
  refine ⟨h.N, (fun j => h.a j + 2 * h.re_b j + h.q j), h.normSq,
    normSqLimit, h.cofinal, h.reproducesZeroQuadratic, hnorm, ?_⟩
  intro j
  have hshift : 0 ≤ h.μ j * (h.nv j ^ 2 + h.nw j ^ 2) :=
    mul_nonneg (h.shiftNonnegative j)
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  calc
    -(FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 (h.N j)) *
        h.normSq j ≤ h.a j - h.μ j * h.nv j ^ 2 -
          h.β j / (h.c j - h.μ j) := h.schurLower j
    _ ≤ h.a j + 2 * h.re_b j + h.q j -
          h.μ j * (h.nv j ^ 2 + h.nw j ^ 2) :=
      AEGIS.RHFeshbachCoreV1.feshbach_lower
        (h.a j) (h.re_b j) (h.q j) (h.nv j) (h.nw j)
        (h.β j) (h.c j) (h.μ j)
        (h.tailNonnegative j) (h.tailCoercivity j)
        (h.crossBound j) (h.betaNonnegative j) (h.shiftBelowGap j)
    _ ≤ h.a j + 2 * h.re_b j + h.q j := sub_le_self _ hshift

/-- The packet-indexed existing Gram/Feshbach data fill the exact
cofinal-consumer interface, provided convergence of their norm squares. -/
theorem every_packet_certificate_of_schur_norm_families
    (h : ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g →
      ∃ f : PacketSchurFamily g,
        ∃ normSqLimit : ℝ, Tendsto f.normSq atTop (𝓝 normSqLimit)) :
    EveryPacketCofinalLowerCertificate := by
  intro g hm
  obtain ⟨f, limit, hnorm⟩ := h g hm
  exact cofinal_certificate_of_packet_schur g f limit hnorm

/-- Actual Mathlib RH target reached from the existing typed Schur data.
The universally quantified concrete family remains an explicit argument. -/
theorem riemannHypothesis_of_schur_norm_families
    (h : ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g →
      ∃ f : PacketSchurFamily g,
        ∃ normSqLimit : ℝ, Tendsto f.normSq atTop (𝓝 normSqLimit)) :
    RiemannHypothesis :=
  riemannHypothesis_of_cofinal_lower_certificates
    (every_packet_certificate_of_schur_norm_families h)

/-- The exact negative Weil Gram form of two actual packets has
    the three Schur block coefficients with the genuine mixed term.
    All values come from the original arithmetic B, not free real parameters. -/
theorem actual_two_block_gram_coefficients
    (u v : WeilCompactSmoothGV1) :
    -(AEGIS.WeilMixedAlgebraV2.B
        (AEGIS.WeilMixedAlgebraV2.addPacket u v)
        (AEGIS.WeilMixedAlgebraV2.addPacket u v)).re =
      -(AEGIS.WeilMixedAlgebraV2.B u u).re +
      2 * (-(AEGIS.WeilMixedAlgebraV2.B u v).re) +
      -(AEGIS.WeilMixedAlgebraV2.B v v).re := by
  rw [AEGIS.WeilMixedAlgebraV2.B_add_left,
      AEGIS.WeilMixedAlgebraV2.B_add_right,
      AEGIS.WeilMixedAlgebraV2.B_add_right,
      AEGIS.WeilMixedAlgebraV2.B_hermitian u v]
  simp only [Complex.add_re, Complex.neg_re, Complex.conj_re]
  ring

/-- The same actual two-block decomposition is an identity for the
    canonical nontrivial-zeta-zero quadratic, not only the arithmetic side. -/
theorem actual_two_block_zero_quadratic_coefficients
    (u v : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1
      (AEGIS.WeilMixedAlgebraV2.addPacket u v)) :
    (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1
        (WeilAutocorrelationV1
          (AEGIS.WeilMixedAlgebraV2.addPacket u v)) rho).re =
      -(AEGIS.WeilMixedAlgebraV2.B u u).re +
      2 * (-(AEGIS.WeilMixedAlgebraV2.B u v).re) +
      -(AEGIS.WeilMixedAlgebraV2.B v v).re := by
  have hEF :=
    AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_explicit_formula_v10
      (AEGIS.WeilMixedAlgebraV2.addPacket u v) hm
  change AEGIS.WeilMixedAlgebraV2.B
    (AEGIS.WeilMixedAlgebraV2.addPacket u v)
    (AEGIS.WeilMixedAlgebraV2.addPacket u v) =
      -(∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1
          (WeilAutocorrelationV1
            (AEGIS.WeilMixedAlgebraV2.addPacket u v)) rho) at hEF
  have hre := congrArg Complex.re hEF
  simp only [Complex.neg_re] at hre
  rw [← actual_two_block_gram_coefficients u v]
  linarith

/-- Source-bound two-block Feshbach inequality: the diagonal, mixed,
and tail Schur entries are the actual arithmetic Weil Gram values.
The equality with the genuine zeta-zero quadratic comes from the
repository's explicit formula; no surrogate bilinear form is introduced. -/
theorem actual_two_block_feshbach_lower
    (u v : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1
      (AEGIS.WeilMixedAlgebraV2.addPacket u v))
    (nv nw β c μ : ℝ)
    (hnw : 0 ≤ nw)
    (hq : c * nw ^ 2 ≤ -(AEGIS.WeilMixedAlgebraV2.B v v).re)
    (hb : (-(AEGIS.WeilMixedAlgebraV2.B u v).re) ^ 2 ≤ β * nw ^ 2)
    (hβ : 0 ≤ β)
    (hμ : μ < c) :
    -(AEGIS.WeilMixedAlgebraV2.B u u).re -
        μ * nv ^ 2 - β / (c - μ) ≤
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1
          (WeilAutocorrelationV1
            (AEGIS.WeilMixedAlgebraV2.addPacket u v)) rho).re -
        μ * (nv ^ 2 + nw ^ 2) := by
  rw [actual_two_block_zero_quadratic_coefficients u v hm]
  exact AEGIS.RHFeshbachCoreV1.feshbach_lower
    (-(AEGIS.WeilMixedAlgebraV2.B u u).re)
    (-(AEGIS.WeilMixedAlgebraV2.B u v).re)
    (-(AEGIS.WeilMixedAlgebraV2.B v v).re)
    nv nw β c μ hnw hq hb hβ hμ

/-- A genuine two-block Schur certificate bounds the actual zero sum.
The error and its squared norm remain explicit; this is the finite
source-bound inequality consumed by the cofinal limit argument. -/
theorem actual_two_block_zero_quadratic_schur_bound
    (u v : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1
      (AEGIS.WeilMixedAlgebraV2.addPacket u v))
    (nv nw β c μ eps normSq : ℝ)
    (hnw : 0 ≤ nw)
    (hq : c * nw ^ 2 ≤ -(AEGIS.WeilMixedAlgebraV2.B v v).re)
    (hb : (-(AEGIS.WeilMixedAlgebraV2.B u v).re) ^ 2 ≤ β * nw ^ 2)
    (hβ : 0 ≤ β)
    (hμ : μ < c)
    (hμ0 : 0 ≤ μ)
    (hSchur :
      -(eps) * normSq ≤
        -(AEGIS.WeilMixedAlgebraV2.B u u).re -
          μ * nv ^ 2 - β / (c - μ)) :
    -(eps) * normSq ≤
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1
          (WeilAutocorrelationV1
            (AEGIS.WeilMixedAlgebraV2.addPacket u v)) rho).re := by
  have hshift : 0 ≤ μ * (nv ^ 2 + nw ^ 2) :=
    mul_nonneg hμ0 (add_nonneg (sq_nonneg _) (sq_nonneg _))
  calc
    -(eps) * normSq ≤
        -(AEGIS.WeilMixedAlgebraV2.B u u).re -
          μ * nv ^ 2 - β / (c - μ) := hSchur
    _ ≤
        (∑' rho : RiemannNontrivialZeroIndexV2,
          WeilZeroIndexSummandV1
            (WeilAutocorrelationV1
              (AEGIS.WeilMixedAlgebraV2.addPacket u v)) rho).re -
          μ * (nv ^ 2 + nw ^ 2) :=
      actual_two_block_feshbach_lower u v hm nv nw β c μ hnw hq hb hβ hμ
    _ ≤ _ := sub_le_self _ hshift

/-- The exact canonical zeta-zero quadratic of an actual finite packet
sum is the negative real part of its *full* mixed Weil Gram matrix.
This is the literal explicit formula, not a surrogate PSD model. -/
theorem actual_zero_quadratic_eq_neg_finite_gram
    {n : ℕ}
    (z : Fin (n + 1) → ℂ)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 (AEGIS.RHGramExpansionV13.packetSum z gs)) :
    (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1
        (WeilAutocorrelationV1 (AEGIS.RHGramExpansionV13.packetSum z gs))
        rho).re =
      -(∑ i, ∑ j,
        z i * star (z j) * AEGIS.WeilMixedAlgebraV2.B (gs i) (gs j)).re := by
  have hEF :=
    AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_explicit_formula_v10
      (AEGIS.RHGramExpansionV13.packetSum z gs) hm
  change
    AEGIS.WeilMixedAlgebraV2.B
      (AEGIS.RHGramExpansionV13.packetSum z gs)
      (AEGIS.RHGramExpansionV13.packetSum z gs) =
      -(∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1
          (WeilAutocorrelationV1 (AEGIS.RHGramExpansionV13.packetSum z gs))
          rho) at hEF
  rw [AEGIS.RHGramExpansionV13.B_packetSum] at hEF
  have hre := congrArg Complex.re hEF
  simp only [Complex.neg_re] at hre
  linarith

/-- Verified finite-dimensional Gram/Gershgorin data control the *actual*
zeta-zero expression, including all off-diagonal arithmetic interactions. -/
theorem actual_zero_quadratic_nonnegative_of_gram_bounds
    {n : ℕ}
    (z : Fin (n + 1) → ℂ)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 (AEGIS.RHGramExpansionV13.packetSum z gs))
    (D E S : ℝ)
    (hE : 0 ≤ E)
    (c : ℕ → ℝ)
    (hc : ∀ k, 0 ≤ c k)
    (hdiag : ∀ i,
      D * E ≤ -(AEGIS.WeilMixedAlgebraV2.B (gs i) (gs i)).re)
    (hcross : ∀ i j, i ≠ j →
      ‖AEGIS.WeilMixedAlgebraV2.B (gs i) (gs j)‖ ≤
        c (Nat.dist i j) * E)
    (hrow : ∀ i : Fin (n + 1),
      AEGIS.RHGramExpansionV13.rowSum c i ≤ S)
    (hmargin : S ≤ D) :
    0 ≤
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1
          (WeilAutocorrelationV1 (AEGIS.RHGramExpansionV13.packetSum z gs))
          rho).re := by
  have hbound := AEGIS.RHGramExpansionV13.gram_re_le
    z gs D E S hE c hc hdiag hcross hrow
  rw [AEGIS.RHGramExpansionV13.B_packetSum] at hbound
  have hcoeff : 0 ≤ (∑ i, ‖z i‖ ^ 2) := by
    apply Finset.sum_nonneg
    intro i hi
    positivity
  have hnonneg : 0 ≤ (D - S) * E * (∑ i, ‖z i‖ ^ 2) :=
    mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hmargin) hE) hcoeff
  rw [actual_zero_quadratic_eq_neg_finite_gram z gs hm]
  linarith

end AEGIS.RHCofinalSchurAdapterV1

#print axioms AEGIS.RHCofinalSchurAdapterV1.cofinal_certificate_of_packet_schur
#print axioms AEGIS.RHCofinalSchurAdapterV1.every_packet_certificate_of_schur_norm_families
#print axioms AEGIS.RHCofinalSchurAdapterV1.riemannHypothesis_of_schur_norm_families
#print axioms AEGIS.RHCofinalSchurAdapterV1.actual_two_block_gram_coefficients
#print axioms AEGIS.RHCofinalSchurAdapterV1.actual_two_block_zero_quadratic_coefficients
#print axioms AEGIS.RHCofinalSchurAdapterV1.actual_two_block_feshbach_lower
#print axioms AEGIS.RHCofinalSchurAdapterV1.actual_two_block_zero_quadratic_schur_bound
#print axioms AEGIS.RHCofinalSchurAdapterV1.actual_zero_quadratic_eq_neg_finite_gram
#print axioms AEGIS.RHCofinalSchurAdapterV1.actual_zero_quadratic_nonnegative_of_gram_bounds
