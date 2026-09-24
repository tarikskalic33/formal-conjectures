import RHLiWeightedPairedTargetV1
import Mathlib.Tactic

/-!
AEGIS Ω — exact Laurent form of the provider's paired Li summand.

For a nontrivial zero rho define
  w(rho) = 1 - 1 / rho.

The functional-equation pairing rho ↦ 1-rho sends w to w⁻¹, so the
provider's paired Li summand is exactly

  T_n(rho) = 2 - w(rho)^(-(n+1)) - w(rho)^(n+1).

This is pure algebra over the provider's already-verified paired-zero
involution. It proves no positivity and no RH claim.

AUTHORITY_EFFECT = NONE
RH = NOT_PROVEN
-/

open Complex

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHLiPairedLaurentV1

open LiCriterion

def liMobiusV1 (rho : LiCriterion.NontrivialZero) : ℂ :=
  1 - 1 / rho.val

theorem liMobius_ne_zero_v1 (rho : LiCriterion.NontrivialZero) :
    liMobiusV1 rho ≠ 0 := by
  intro h
  have hr0 : (rho.val : ℂ) ≠ 0 := LiCriterion.NontrivialZero.ne_zero rho
  have hr1 : (rho.val : ℂ) ≠ 1 := LiCriterion.NontrivialZero.ne_one rho
  unfold liMobiusV1 at h
  have hdiv : (1 : ℂ) / rho.val = 1 := sub_eq_zero.mp h
  have hone : (1 : ℂ) = rho.val := by
    simpa using (div_eq_iff hr0).mp hdiv
  exact hr1 hone.symm

theorem liMobius_pairedZero_eq_inv_v1
    (rho : LiCriterion.NontrivialZero) :
    liMobiusV1 (LiCriterion.pairedZero rho) =
      (liMobiusV1 rho)⁻¹ := by
  have hr0 : (rho.val : ℂ) ≠ 0 := LiCriterion.NontrivialZero.ne_zero rho
  have hr1 : (rho.val : ℂ) ≠ 1 := LiCriterion.NontrivialZero.ne_one rho
  have h1r : (1 : ℂ) - rho.val ≠ 0 := sub_ne_zero.mpr hr1.symm
  have hw :
      (1 : ℂ) - 1 / rho.val ≠ 0 := by
    simpa [liMobiusV1] using liMobius_ne_zero_v1 rho
  unfold liMobiusV1
  rw [LiCriterion.pairedZero_val]
  field_simp [hr0, h1r, hw]
  ring

theorem liPairedSummand_eq_laurent_v1
    (n : ℕ) (rho : LiCriterion.NontrivialZero) :
    LiCriterion.liPairedSummand n rho =
      (2 : ℂ) -
        (liMobiusV1 rho) ^ (-(n + 1 : ℤ)) -
        (liMobiusV1 rho) ^ (n + 1) := by
  unfold LiCriterion.liPairedSummand LiCriterion.liSummand
  change
    (1 - (liMobiusV1 rho) ^ (-(n + 1 : ℤ))) +
      (1 - (liMobiusV1 (LiCriterion.pairedZero rho)) ^ (-(n + 1 : ℤ))) =
        (2 : ℂ) -
          (liMobiusV1 rho) ^ (-(n + 1 : ℤ)) -
          (liMobiusV1 rho) ^ (n + 1)
  rw [liMobius_pairedZero_eq_inv_v1]
  rw [inv_zpow']
  simp only [neg_neg, zpow_natCast]
  ring

end AEGIS.RHLiPairedLaurentV1

#print axioms AEGIS.RHLiPairedLaurentV1.liMobius_ne_zero_v1
#print axioms AEGIS.RHLiPairedLaurentV1.liMobius_pairedZero_eq_inv_v1
#print axioms AEGIS.RHLiPairedLaurentV1.liPairedSummand_eq_laurent_v1
