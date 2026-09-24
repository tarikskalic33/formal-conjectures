import RHDeepMindTerminalV1
import Lc.LiCriterion.GenusOnePairedSumFormula
import Lc.LiCriterion.HadamardBridge
import Lc.LiCriterion.HadamardSummabilityBridge
import Lc.LiCriterion.XiOrderBridge

/-!
AEGIS Ω — explicit weighted paired-sum target for the exact DeepMind Li terminal.

This module rewrites the sole remaining target
`AEGIS.RHDeepMindTerminalV1.LiNonnegativityV1` into the provider's
multiplicity-aware paired zero sum.  It introduces no positivity assumption.

For each provider index `n`:
  taylorCoeff riemannXi n
    = (1/2) * Σ' ρ, mult(ρ) * liPairedSummand n ρ.

Thus the exact external RH target is reduced to nonnegativity of the real
part of these explicit weighted paired sums.

AUTHORITY_EFFECT = NONE
RH = NOT_PROVEN
-/

open Complex
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHLiWeightedPairedTargetV1

open LiCriterion
open AEGIS.RHDeepMindTerminalV1

/-- The exact multiplicity-aware paired-zero expression for the provider's
`n`-th Taylor/Li coefficient. -/
def WeightedPairedLiSumV1 (n : ℕ) : ℂ :=
  (2⁻¹ : ℂ) *
    ∑' ρ : LiCriterion.NontrivialZero,
      (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
        LiCriterion.liPairedSummand n ρ

/-- All analytic prerequisites for the weighted paired-sum formula are already
unconditional in the pinned provider. -/
theorem taylorCoeff_eq_weighted_paired_sum_v1 (n : ℕ) :
    LiCriterion.taylorCoeff LiCriterion.riemannXi n =
      WeightedPairedLiSumV1 n := by
  unfold WeightedPairedLiSumV1
  exact
    LiCriterion.weighted_paired_sum_formula_of_standard_hypotheses
      (LiCriterion.xi_weighted_genus_one_of_hadamard_order_one
        LiCriterion.xi_hasFiniteOrder
        LiCriterion.xi_order_le_one)
      (LiCriterion.xi_factorization_prod_with_multiplicity_of_hadamard_order_one
        LiCriterion.xi_hasFiniteOrder
        LiCriterion.xi_order_le_one)
      n

/-- Explicit paired-sum form of the sole remaining DeepMind target. -/
def WeightedPairedNonnegativityV1 : Prop :=
  ∀ n : ℕ, 0 ≤ (WeightedPairedLiSumV1 n).re

/-- The opaque derivative target and the explicit weighted paired-zero target
are definitionally bridged by the provider's kernel theorem. -/
theorem li_nonnegativity_iff_weighted_paired_v1 :
    LiNonnegativityV1 ↔ WeightedPairedNonnegativityV1 := by
  constructor
  · intro h n
    unfold WeightedPairedNonnegativityV1 WeightedPairedLiSumV1
    rw [← taylorCoeff_eq_weighted_paired_sum_v1]
    exact h n
  · intro h n
    unfold WeightedPairedNonnegativityV1 at h
    rw [taylorCoeff_eq_weighted_paired_sum_v1]
    exact h n

/-- Closing the explicit weighted paired sums closes the exact Mathlib /
FormalConjectures Riemann-hypothesis target. -/
theorem weighted_paired_nonnegativity_closes_rh_v1
    (h : WeightedPairedNonnegativityV1) :
    RiemannHypothesis :=
  li_nonnegativity_closes_rh_v1
    (li_nonnegativity_iff_weighted_paired_v1.mpr h)

end AEGIS.RHLiWeightedPairedTargetV1

#print axioms AEGIS.RHLiWeightedPairedTargetV1.taylorCoeff_eq_weighted_paired_sum_v1
#print axioms AEGIS.RHLiWeightedPairedTargetV1.li_nonnegativity_iff_weighted_paired_v1
#print axioms AEGIS.RHLiWeightedPairedTargetV1.weighted_paired_nonnegativity_closes_rh_v1
