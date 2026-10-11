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

/-!
AEGIS Ω — location-independent RH proof entrypoint.

This module uses Lean module names, never filesystem-relative imports.
Its source file can be located anywhere; the build must provide the module
search path (LEAN_PATH) containing the compiled dependency closure.

This intentionally exposes the exact remaining premise instead of claiming
that the Riemann Hypothesis follows without it.
-/

import RHRestrictedWeilCriterionV13

set_option autoImplicit false

namespace AEGIS.AEGISRHRootV1

open AEGIS.RHMillenniumGateV10

/-- The verified bridge from the universal zero-quadratic statement to
Mathlib's exact RiemannHypothesis proposition. The premise is not discharged
by this entrypoint. -/
theorem riemann_hypothesis_of_universal_zero_quadratic
    (h : UniversalZeroQuadraticNonnegativeV10) :
    RiemannHypothesis :=
  AEGIS.RHRestrictedWeilCriterionV13.universal_zero_quadratic_implies_mathlib_rh_v13 h

end AEGIS.AEGISRHRootV1

#print axioms AEGIS.AEGISRHRootV1.riemann_hypothesis_of_universal_zero_quadratic
