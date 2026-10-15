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

open Filter Topology

namespace AEGIS.RHFeshbachScaledErrorV1

theorem nonneg_of_invFourth_scaled_error
    {N : ℕ → ℕ} {q normSq : ℕ → ℝ} {Q : ℝ}
    (hq : Tendsto q atTop (𝓝 Q))
    (hscaled : Tendsto
      (fun j => FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 (N j) *
        normSq j) atTop (𝓝 0))
    (hlower : ∀ j,
      -(FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 (N j)) *
        normSq j ≤ q j) :
    0 ≤ Q := by
  have hzero : Tendsto
      (fun j => -(FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 (N j)) *
        normSq j) atTop (𝓝 0) := by
    simpa only [neg_mul, neg_zero] using hscaled.neg
  exact FormalConjecturesUtil.FixedWindowLimitBridge.nonneg_of_tendsto_lower_bound
    hq hzero hlower

end AEGIS.RHFeshbachScaledErrorV1

#print axioms AEGIS.RHFeshbachScaledErrorV1.nonneg_of_invFourth_scaled_error
