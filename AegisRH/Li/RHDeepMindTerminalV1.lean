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

import AegisLiCriterionRebindV1

/-!
AEGIS Ω — current-head Li terminal for the DeepMind/Mathlib RH target.

The target type is Mathlib's `RiemannHypothesis`, which is exactly the
predicate used by Google DeepMind Formal Conjectures Millennium RH.

This module performs no proof promotion. It isolates the sole remaining
producer obligation after the unconditional Li criterion has been rebound:
nonnegativity of every Li–Keiper coefficient.
-/

namespace AEGIS.RHDeepMindTerminalV1

def LiNonnegativityV1 : Prop :=
  ∀ n : ℕ, 0 ≤ (LiCriterion.taylorCoeff LiCriterion.riemannXi n).re

theorem li_nonnegativity_iff_rh_v1 :
    LiNonnegativityV1 ↔ RiemannHypothesis := by
  simpa [LiNonnegativityV1] using
    AegisRhLiBridge.aegis_li_criterion_rh_iff_v1.symm

theorem li_nonnegativity_closes_rh_v1
    (h : LiNonnegativityV1) : RiemannHypothesis :=
  (li_nonnegativity_iff_rh_v1).mp h

theorem rh_implies_li_nonnegativity_v1
    (h : RiemannHypothesis) : LiNonnegativityV1 :=
  (li_nonnegativity_iff_rh_v1).mpr h

end AEGIS.RHDeepMindTerminalV1

#print axioms AEGIS.RHDeepMindTerminalV1.li_nonnegativity_iff_rh_v1
#print axioms AEGIS.RHDeepMindTerminalV1.li_nonnegativity_closes_rh_v1
