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
import RHFeshbachWeilClosureV2

/-!
Construction candidate on the existing certified narrow-window class.
No unconditional RH declaration is asserted. Exact-head CI must check this file.
-/

open Filter Topology
open scoped BigOperators
noncomputable section

namespace AEGIS.RHAssemblyV1

open AEGIS.RHFeshbachWeilClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2

def narrow_window_schur_family
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (hw : AEGIS.WeilWindowExhaustionV1.LogWindowContainsV1 g (693 / 2000)) :
    PacketSchurFamily g := by
  let A : ℝ := -(B g g).re
  let E : ℝ := energy g.1
  have hE : 0 ≤ E := energy_nonnegative g.1
  have hA : 0 ≤ A := by
    change 0 ≤ -(WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re
    exact neg_nonneg.mpr
      (AEGIS.RHWindow693Over2000V1.window_693_over_2000_arithmetic_nonpositive_v1
        g hm hw)
  have hrepr : A = (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
    have h :=
      AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_explicit_formula_v10
        g hm
    change B g g = -(∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho) at h
    have hre := congrArg Complex.re h
    simp only [Complex.neg_re] at hre
    dsimp [A]
    linarith
  refine {
    N := fun j => j
    a := fun _ => A
    re_b := fun _ => 0
    q := fun _ => 0
    nv := fun _ => Real.sqrt E
    nw := fun _ => 0
    β := fun _ => 0
    c := fun _ => 1
    μ := fun _ => 0
    normSq := fun _ => E
    normUpper := E
    cofinal := tendsto_id
    reproducesZeroQuadratic := ?_
    eventuallyBounded := Eventually.of_forall (fun _ => le_rfl)
    shiftNonnegative := fun _ => le_rfl
    tailNonnegative := fun _ => le_rfl
    tailCoercivity := ?_
    crossBound := ?_
    betaNonnegative := fun _ => le_rfl
    shiftBelowGap := ?_
    schurLower := ?_
  }
  · simp [hrepr]
  · intro j
    norm_num
  · intro j
    norm_num
  · intro j
    norm_num
  · intro j
    have he : 0 ≤ FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 j := by
      unfold FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError
      positivity
    have hlower :
        -(FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 j) * E ≤ A :=
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr he) hE).trans hA
    simpa using hlower

theorem narrow_window_schur_norm_family
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (hw : AEGIS.WeilWindowExhaustionV1.LogWindowContainsV1 g (693 / 2000)) :
    ∃ f : PacketSchurFamily g,
      ∃ L : ℝ, Tendsto f.normSq atTop (𝓝 L) := by
  refine ⟨narrow_window_schur_family g hm hw, energy g.1, ?_⟩
  change Tendsto (fun _ : ℕ => energy g.1) atTop (𝓝 (energy g.1))
  exact tendsto_const_nhds

end AEGIS.RHAssemblyV1

#print axioms AEGIS.RHAssemblyV1.narrow_window_schur_family
#print axioms AEGIS.RHAssemblyV1.narrow_window_schur_norm_family
