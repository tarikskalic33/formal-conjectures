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
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
https://www.apache.org/licenses/LICENSE-2.0
-/
import AEGISOverlay.RHOptimizedSchurGlobalJoinV1
import AEGISOverlay.RHActualUniversalFineGramV1
import CvSRowTailV1

/-!
# CvS zero-side to genuine actual Weil mixed-defect alignment

Source-exact: the CvS window result supplies a zero-side sign on a specified
packet. The PR #89 fine-Gram constructor supplies a genuine exact finite
reconstruction of that same packet. This file proves the equality joining
those two sides, with no invented matrix bounds or reconstruction assumptions.

The locally proved bridge does not upgrade a restricted window statement
to a universal statement about every packet.
-/

open Finset
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHCvSActualWeilInteropV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.RHGramExpansionV13

/-- Genuine actual-Weil diagonal + mixed defect is exactly the negative
canonical zero-side quadratic, for a constructed finite partition of any
moment-zero source. No inequality or Schur row estimate is assumed. -/
theorem actual_fine_mixed_defect_eq_neg_zero_side
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs +
        ∑ i, (B (gs i) (gs i)).re) =
        -(∑' rho : RiemannNontrivialZeroIndexV2,
          WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  obtain ⟨n, gs, _hmom, _hd, hpacket, hgram⟩ :=
    AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram g hm
  refine ⟨n, gs, hpacket, ?_⟩
  have hformula :=
    AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_explicit_formula_v10 g hm
  have hreal := congrArg Complex.re hformula
  simp only [Complex.neg_re] at hreal
  calc
    _ = (∑ i, ∑ j, B (gs i) (gs j)).re := by
      simp [AEGIS.RHActualMixedDefectV1.actualMixedDefect]
    _ = (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re := hgram.symm
    _ = _ := by simpa using hreal

/-- Every CvS-derived zero-side proof for a particular packet yields its
actual source-exact signed mixed-defect certificate, without hselect,
hglobal, artificial diagonal row costs, or changing the original packet. -/
theorem actual_signed_budget_of_zero_side
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (hzero : 0 ≤
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re) :
    ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
        -(∑ i, (B (gs i) (gs i)).re) := by
  obtain ⟨n, gs, hpacket, hid⟩ :=
    actual_fine_mixed_defect_eq_neg_zero_side g hm
  refine ⟨n, gs, hpacket, ?_⟩
  linarith

end AEGIS.RHCvSActualWeilInteropV1

#check AEGIS.CvSRowTailV1.window_of_certificate_tail
#print axioms AEGIS.RHCvSActualWeilInteropV1.actual_fine_mixed_defect_eq_neg_zero_side
#print axioms AEGIS.RHCvSActualWeilInteropV1.actual_signed_budget_of_zero_side
