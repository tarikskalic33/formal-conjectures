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

import Lc.LiCriterion.XiOrderBridge

/-!
AEGIS Ω — exact provider-bound Li criterion bridge v1.

The imported provider theorem is compiled only after rebinding its original
Mathlib pin to the AEGIS Lean/Mathlib environment and applying the separately
audited three-token compatibility patch in the hosted verification lane.

This module does not prove the Li-coefficient nonnegativity statement and
therefore does not prove the Riemann Hypothesis.  It only exposes the already
kernel-checked biconditional against Mathlib's `RiemannHypothesis` under an
AEGIS-owned theorem name.
-/

namespace AegisRhLiBridge

/-- The provider's unconditional Li criterion, rebound into the AEGIS evidence
surface. This is an equivalence theorem, not a proof of either side. -/
theorem aegis_li_criterion_rh_iff_v1 :
    RiemannHypothesis ↔
      (∀ n : ℕ, 0 ≤ (LiCriterion.taylorCoeff LiCriterion.riemannXi n).re) :=
  LiCriterion.li_criterion_rh_iff

end AegisRhLiBridge

#print axioms AegisRhLiBridge.aegis_li_criterion_rh_iff_v1
