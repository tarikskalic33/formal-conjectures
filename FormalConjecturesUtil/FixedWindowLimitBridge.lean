# Copyright 2025 The Formal Conjectures Authors.
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import Mathlib

/-!
# Fixed-window limit and cofinal-window bridge

Abstract order-theoretic pieces used by the AEGIS fixed-window Weil lane.

The first theorem packages the finite-to-limit step: if a sequence of
quadratic values converges to the target value and is bounded below by a
second sequence converging to zero, then the target value is nonnegative.

The second package records that, for any monotone window predicate, the
windows `R = n * π` are cofinal among all positive real windows.

No matrix positivity premise is manufactured here.
-/

namespace FormalConjecturesUtil.FixedWindowLimitBridge

open Filter Topology

theorem nonneg_of_tendsto_lower_bound
    {a lower : ℕ → ℝ} {A : ℝ}
    (ha : Tendsto a atTop (𝓝 A))
    (hlower : Tendsto lower atTop (𝓝 0))
    (hle : ∀ n, lower n ≤ a n) :
    0 ≤ A :=
  le_of_tendsto_of_tendsto' hlower ha hle

theorem nonneg_of_vanishing_error_norm
    {q eps normSq : ℕ → ℝ} {Q normSqLimit : ℝ}
    (hq : Tendsto q atTop (𝓝 Q))
    (heps : Tendsto eps atTop (𝓝 0))
    (hnorm : Tendsto normSq atTop (𝓝 normSqLimit))
    (hlower : ∀ n, -(eps n) * normSq n ≤ q n) :
    0 ≤ Q := by
  have hvanish :
      Tendsto (fun n => -(eps n) * normSq n) atTop (𝓝 0) := by
    simpa using heps.neg.mul hnorm
  exact nonneg_of_tendsto_lower_bound hq hvanish hlower

theorem all_positive_windows_of_pi_nat_windows
    (P : ℝ → Prop)
    (hmono : ∀ {R₁ R₂ : ℝ}, R₁ ≤ R₂ → P R₂ → P R₁)
    (hpi : ∀ n : ℕ, 0 < n → P ((n : ℝ) * Real.pi)) :
    ∀ R : ℝ, 0 < R → P R := by
  intro R hR
  obtain ⟨n, hn⟩ := exists_nat_gt (R / Real.pi)
  have hnR : (0 : ℝ) < (n : ℝ) :=
    (div_pos hR Real.pi_pos).trans hn
  have hnNat : 0 < n := by
    exact_mod_cast hnR
  have hRlt : R < (n : ℝ) * Real.pi :=
    (div_lt_iff₀ Real.pi_pos).mp hn
  exact hmono hRlt.le (hpi n hnNat)

theorem all_positive_windows_iff_pi_nat_windows
    (P : ℝ → Prop)
    (hmono : ∀ {R₁ R₂ : ℝ}, R₁ ≤ R₂ → P R₂ → P R₁) :
    (∀ R : ℝ, 0 < R → P R) ↔
      ∀ n : ℕ, 0 < n → P ((n : ℝ) * Real.pi) := by
  constructor
  · intro h n hn
    apply h
    exact mul_pos (by exact_mod_cast hn) Real.pi_pos
  · exact all_positive_windows_of_pi_nat_windows P hmono

end FormalConjecturesUtil.FixedWindowLimitBridge
