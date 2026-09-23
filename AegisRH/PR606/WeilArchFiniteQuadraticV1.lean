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

import WeilArchSineKernelIntegerV1

/-!
AEGIS Ω — fixed-T finite Archimedean quadratic module boundary v1.

The actual definitions and proofs live in `WeilArchSineKernelIntegerV1`, where
they were proved directly from the true Archimedean sine source and the
rank-two Cauchy entry identity.  This file deliberately re-exports that
already-kernel-checked surface as the preregistered module boundary.

It adds no theorem and grants no stronger claim.  Continuous T-integration,
the full Archimedean weight, tail operator order, full finite Galerkin PSD,
formula-to-Weil operator identity, global Weil positivity, RH, repository
admission, merge, and authority effects remain outside this module.
-/

#check WeilArchFiniteQuadraticV1
#check weil_arch_finite_quadratic_scaled_cauchy_v1
#check weil_arch_scale_nonnegative_v1
#check weil_arch_finite_quadratic_nonnegative_v1
#check weil_arch_sine_finite_quadratic_nonnegative_v1
