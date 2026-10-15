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

import RHFeshbachCoreV1
import FormalConjecturesUtil.FixedWindowLimitBridge
import WeilRHImpliesFinalSignV13
import RHFinalClosureSpineV1
import WeilWindowExhaustionV1
import WeilAutocorrelationExplicitFormulaV10
import RHGramExpansionV13
import RHWindow693Over2000V1
import Mathlib

/-!
# The cofinal Feshbach / actual Weil packet assembly

The earlier fusion required norm convergence and shifted-form convergence.
Here the norm-square sequence is only eventually bounded above, while a
nonnegative spectral shift permits transfer to the unshifted quadratic form.
The theorem at the end is conditional on genuinely constructing the stated
Schur families for all relevant Weil test packets. It is not a proof of RH.
-/

open Filter Topology
open scoped BigOperators

namespace AEGIS.RHFeshbachWeilClosureV2

theorem nonneg_of_vanishing_error_eventually_bounded
    {q eps normSq : ℕ → ℝ} {Q C : ℝ}
    (hq : Tendsto q atTop (𝓝 Q))
    (heps : Tendsto eps atTop (𝓝 0))
    (hepsNonneg : ∀ j, 0 ≤ eps j)
    (hbound : ∀ᶠ j in atTop, normSq j ≤ C)
    (hlower : ∀ j, -(eps j) * normSq j ≤ q j) :
    0 ≤ Q := by
  have hconst : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) :=
    tendsto_const_nhds
  have hzero : Tendsto (fun j => -(eps j) * C) atTop (𝓝 0) := by
    simpa using heps.neg.mul hconst
  apply le_of_tendsto_of_tendsto hzero hq
  filter_upwards [hbound] with j hj
  have hmul : eps j * normSq j ≤ eps j * C :=
    mul_le_mul_of_nonneg_left hj (hepsNonneg j)
  calc
    -(eps j) * C = -(eps j * C) := by ring
    _ ≤ -(eps j * normSq j) := neg_le_neg hmul
    _ = -(eps j) * normSq j := by ring
    _ ≤ q j := hlower j

theorem cofinal_feshbach_unshifted_eventually_bounded_nonnegative
    {N : ℕ → ℕ}
    {a re_b q nv nw β c μ normSq : ℕ → ℝ}
    {Q C : ℝ}
    (hN : Tendsto N atTop atTop)
    (hUnshiftLim : Tendsto
      (fun j => a j + 2 * re_b j + q j) atTop (𝓝 Q))
    (hNormBound : ∀ᶠ j in atTop, normSq j ≤ C)
    (hμ0 : ∀ j, 0 ≤ μ j)
    (hnw : ∀ j, 0 ≤ nw j)
    (hq : ∀ j, c j * nw j ^ 2 ≤ q j)
    (hb : ∀ j, re_b j ^ 2 ≤ β j * nw j ^ 2)
    (hβ : ∀ j, 0 ≤ β j)
    (hμ : ∀ j, μ j < c j)
    (hSchur : ∀ j,
      -(FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 (N j)) *
        normSq j ≤
      a j - μ j * nv j ^ 2 - β j / (c j - μ j)) :
    0 ≤ Q := by
  refine nonneg_of_vanishing_error_eventually_bounded
    hUnshiftLim
    (FormalConjecturesUtil.FixedWindowLimitBridge.tendsto_invFourthError_along_cofinal hN)
    (fun j => ?_) hNormBound (fun j => ?_)
  · unfold FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError
    positivity
  · have hshift : 0 ≤ μ j * (nv j ^ 2 + nw j ^ 2) :=
      mul_nonneg (hμ0 j) (add_nonneg (sq_nonneg _) (sq_nonneg _))
    calc
      -(FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 (N j)) *
          normSq j ≤ a j - μ j * nv j ^ 2 - β j / (c j - μ j) :=
        hSchur j
      _ ≤ a j + 2 * re_b j + q j -
          μ j * (nv j ^ 2 + nw j ^ 2) :=
        AEGIS.RHFeshbachCoreV1.feshbach_lower
          (a j) (re_b j) (q j) (nv j) (nw j) (β j) (c j) (μ j)
          (hnw j) (hq j) (hb j) (hβ j) (hμ j)
      _ ≤ a j + 2 * re_b j + q j := sub_le_self _ hshift

/-- Exact packet-indexed assumptions for the as-yet-unconstructed
cofinal Schur certificates, including analytic identification of the limit. -/
structure PacketSchurFamily (g : WeilCompactSmoothGV1) where
  N : ℕ → ℕ
  a : ℕ → ℝ
  re_b : ℕ → ℝ
  q : ℕ → ℝ
  nv : ℕ → ℝ
  nw : ℕ → ℝ
  β : ℕ → ℝ
  c : ℕ → ℝ
  μ : ℕ → ℝ
  normSq : ℕ → ℝ
  normUpper : ℝ
  cofinal : Tendsto N atTop atTop
  reproducesZeroQuadratic : Tendsto
    (fun j => a j + 2 * re_b j + q j) atTop
    (𝓝 ((∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re))
  eventuallyBounded : ∀ᶠ j in atTop, normSq j ≤ normUpper
  shiftNonnegative : ∀ j, 0 ≤ μ j
  tailNonnegative : ∀ j, 0 ≤ nw j
  tailCoercivity : ∀ j, c j * nw j ^ 2 ≤ q j
  crossBound : ∀ j, re_b j ^ 2 ≤ β j * nw j ^ 2
  betaNonnegative : ∀ j, 0 ≤ β j
  shiftBelowGap : ∀ j, μ j < c j
  schurLower : ∀ j,
    -(FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 (N j)) *
      normSq j ≤
    a j - μ j * nv j ^ 2 - β j / (c j - μ j)

/-- An actual packet Schur family forces the nonnegative *canonical zero sum*
from the repository's explicit-formula language, not an abstract surrogate. -/
theorem packet_zero_quadratic_nonnegative (g : WeilCompactSmoothGV1)
    (h : PacketSchurFamily g) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  exact cofinal_feshbach_unshifted_eventually_bounded_nonnegative
    h.cofinal h.reproducesZeroQuadratic h.eventuallyBounded h.shiftNonnegative
    h.tailNonnegative h.tailCoercivity h.crossBound h.betaNonnegative
    h.shiftBelowGap h.schurLower

/-- The pre-existing V10 concrete autocorrelation explicit formula converts
the actual zero-side sign to the actual Weil arithmetic sign. -/
theorem packet_weil_nonpositive (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (h : PacketSchurFamily g) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0 :=
  (AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
    g hm).mpr
      (packet_zero_quadratic_nonnegative g h)

/-- Direct connection to the existing cofinal-window RH equivalence.
This implication is conditional; no packet family is silently postulated. -/
theorem riemannHypothesis_of_window_schur_families
    (h : ∀ n : ℕ, 0 < n →
      ∀ g : WeilCompactSmoothGV1,
        WeilMomentConditionsV1 g →
        AEGIS.WeilWindowExhaustionV1.LogWindowContainsV1 g
          ((n : ℝ) * Real.pi) →
        PacketSchurFamily g) :
    RiemannHypothesis := by
  have hAll :
      RiemannHypothesis ↔
        ∀ L : ℝ, 0 < L →
          AEGIS.WeilWindowExhaustionV1.WindowArithmeticNonpositiveV1 L :=
    AEGIS.WeilRHImpliesFinalSignV13.rh_iff_final_sign_v13.trans
      (AEGIS.RHFinalClosureV1.final_sign_residual_iff_weil_negativity_v1.trans
        AEGIS.WeilWindowExhaustionV1.weil_compact_smooth_negativity_iff_all_windows_v1)
  apply (hAll.trans
    (FormalConjecturesUtil.FixedWindowLimitBridge.all_positive_windows_iff_pi_nat_windows
      AEGIS.WeilWindowExhaustionV1.WindowArithmeticNonpositiveV1
      (fun {R₁ R₂} hR hWin =>
        AEGIS.WeilWindowExhaustionV1.windowArithmeticNonpositive_mono_v1 hR hWin))).mpr
  intro n hn g hm hw
  exact packet_weil_nonpositive g hm (h n hn g hm hw)


/-!
## Recovered arbitrary-finite-localization budget (existing V13 producer)

This consumes the *existing* exact Gram expansion and row-sum estimate,
without reconstructing their algebra or discarding mixed terms. It applies to
any finite list of actual Weil packets for which the original Gram hypotheses
have been established. The index-distance majorant and its numeric row budget
remain explicit: no universal numerical budget is silently asserted.
-/

/-- The pre-existing Gershgorin row bound, with an admissible one-sided
gap-budget, implies the sign of the *actual* mixed Weil form on an arbitrary
finite packet sum. This is an adapter, not a new Gram/Schur proof. -/
theorem actual_gram_arithmetic_nonpositive
    {n : ℕ} (z : Fin (n + 1) → ℂ)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (D E : ℝ) (hE : 0 ≤ E) (c : ℕ → ℝ)
    (hc : ∀ k, 0 ≤ c k)
    (hdiag : ∀ i, D * E ≤
      -(AEGIS.WeilMixedAlgebraV2.B (gs i) (gs i)).re)
    (hcross : ∀ i j, i ≠ j →
      ‖AEGIS.WeilMixedAlgebraV2.B (gs i) (gs j)‖ ≤ c (Nat.dist i j) * E)
    (hbudget : 2 * ∑ k ∈ Finset.Icc 1 n, c k ≤ D) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1
      (AEGIS.RHGramExpansionV13.packetSum z gs))).re ≤ 0 := by
  have hrow : ∀ i : Fin (n + 1),
      AEGIS.RHGramExpansionV13.rowSum c i ≤ D := by
    intro i
    exact (AEGIS.RHGramExpansionV13.rowSum_le c hc i).trans hbudget
  have hbound :=
    AEGIS.RHGramExpansionV13.gram_re_le
      z gs D E D hE c hc hdiag hcross hrow
  have hsign :
      (AEGIS.WeilMixedAlgebraV2.B
        (AEGIS.RHGramExpansionV13.packetSum z gs)
        (AEGIS.RHGramExpansionV13.packetSum z gs)).re ≤ 0 := by
    simpa using hbound
  change (AEGIS.WeilMixedAlgebraV2.B
    (AEGIS.RHGramExpansionV13.packetSum z gs)
    (AEGIS.RHGramExpansionV13.packetSum z gs)).re ≤ 0
  exact hsign

/-- Exact zero-side consequence of the already-proved arbitrary finite Gram
estimate, using the *existing* V10 explicit formula and genuine moments. -/
theorem actual_gram_zero_quadratic_nonnegative
    {n : ℕ} (z : Fin (n + 1) → ℂ)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (D E : ℝ) (hE : 0 ≤ E) (c : ℕ → ℝ)
    (hc : ∀ k, 0 ≤ c k)
    (hdiag : ∀ i, D * E ≤
      -(AEGIS.WeilMixedAlgebraV2.B (gs i) (gs i)).re)
    (hcross : ∀ i j, i ≠ j →
      ‖AEGIS.WeilMixedAlgebraV2.B (gs i) (gs j)‖ ≤ c (Nat.dist i j) * E)
    (hbudget : 2 * ∑ k ∈ Finset.Icc 1 n, c k ≤ D)
    (hm : WeilMomentConditionsV1 (AEGIS.RHGramExpansionV13.packetSum z gs)) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1
        (WeilAutocorrelationV1 (AEGIS.RHGramExpansionV13.packetSum z gs))
        rho).re := by
  exact (AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
      (AEGIS.RHGramExpansionV13.packetSum z gs) hm).mp
    (actual_gram_arithmetic_nonpositive z gs D E hE c hc
      hdiag hcross hbudget)

/--
A concrete two-source sign assembly for the *actual* zero quadratic.

The first route is the existing unconditional 693/2000 logarithmic window.
The second route uses the existing V13 Gram/Gershgorin mixed-term budget.
Neither branch assumes the sign of the output as an input, and this lemma
does not claim these two certified classes exhaust all Weil packets.
-/
theorem actual_sign_of_certified_window_or_gram
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (h :
      AEGIS.WeilWindowExhaustionV1.LogWindowContainsV1 g (693 / 2000) ∨
      ∃ (n : ℕ) (z : Fin (n + 1) → ℂ)
        (gs : Fin (n + 1) → WeilCompactSmoothGV1)
        (D E : ℝ) (c : ℕ → ℝ),
        g = AEGIS.RHGramExpansionV13.packetSum z gs ∧
        0 ≤ E ∧
        (∀ k, 0 ≤ c k) ∧
        (∀ i, D * E ≤
          -(AEGIS.WeilMixedAlgebraV2.B (gs i) (gs i)).re) ∧
        (∀ i j, i ≠ j →
          ‖AEGIS.WeilMixedAlgebraV2.B (gs i) (gs j)‖ ≤
            c (Nat.dist i j) * E) ∧
        2 * ∑ k ∈ Finset.Icc 1 n, c k ≤ D) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  rcases h with hw | ⟨n, z, gs, D, E, c, hrepr, hE, hc, hd, hx, hb⟩
  · have hsign :=
      AEGIS.RHWindow693Over2000V1.window_693_over_2000_arithmetic_nonpositive_v1
        g hm hw
    exact (AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
      g hm).mp hsign
  · subst g
    exact actual_gram_zero_quadratic_nonnegative z gs D E hE c hc hd hx hb hm

end AEGIS.RHFeshbachWeilClosureV2

#print axioms AEGIS.RHFeshbachWeilClosureV2.nonneg_of_vanishing_error_eventually_bounded
#print axioms AEGIS.RHFeshbachWeilClosureV2.cofinal_feshbach_unshifted_eventually_bounded_nonnegative
#print axioms AEGIS.RHFeshbachWeilClosureV2.packet_zero_quadratic_nonnegative
#print axioms AEGIS.RHFeshbachWeilClosureV2.actual_gram_arithmetic_nonpositive
#print axioms AEGIS.RHFeshbachWeilClosureV2.actual_gram_zero_quadratic_nonnegative
#print axioms AEGIS.RHFeshbachWeilClosureV2.packet_weil_nonpositive
#print axioms AEGIS.RHFeshbachWeilClosureV2.riemannHypothesis_of_window_schur_families

#print axioms AEGIS.RHFeshbachWeilClosureV2.actual_sign_of_certified_window_or_gram
