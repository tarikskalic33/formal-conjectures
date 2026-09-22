import RestrictedWeilCriterionResidueCoefficientV11
import RestrictedWeilCriterionPoleIsolationV10
import MeromorphicIdentityPreconnectedV11
import WeilRHImpliesFinalSignV11
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic

open Set Filter Topology Complex
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.V13Scratch

open AEGIS.RHFinalClosureV1
open AEGIS.RHMillenniumGateV10
open AEGIS.RestrictedWeilCriterionLaplaceV10
open AEGIS.RestrictedWeilCriterionPoleIsolationV10
open AEGIS.RestrictedWeilCriterionResidueCoefficientV11
open AEGIS.MeromorphicIdentityPreconnectedV11

def RightHalfPlaneV13 : Set ℂ := {w : ℂ | 0 < w.re}

theorem rightHalfPlane_isPreconnected_v13 :
    IsPreconnected RightHalfPlaneV13 := by
  simpa [RightHalfPlaneV13] using
    (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected

theorem final_sign_to_universal_zero_quadratic_v13
    (h : FinalSignResidualV1) :
    UniversalZeroQuadraticNonnegativeV10 :=
  universal_zero_quadratic_iff_final_sign_v10.mpr h

theorem laplace_cauchy_seed_eventuallyEq_v13
    (g : WeilCompactSmoothGV1) :
    ZeroKernelLaplaceV10 g =ᶠ[𝓝 (1 : ℂ)]
      ZeroCauchyTransformV10 g := by
  let S : Set ℂ := {w : ℂ | (1 / 2 : ℝ) < w.re}
  have hSopen : IsOpen S := by
    simpa [S] using
      Complex.continuous_re.isOpen_preimage (Ioi (1 / 2 : ℝ)) isOpen_Ioi
  have h1S : (1 : ℂ) ∈ S := by
    simp [S]
  filter_upwards [hSopen.mem_nhds h1S] with w hw
  exact zero_kernel_laplace_eq_cauchy_v10 g hw

end AEGIS.V13Scratch
