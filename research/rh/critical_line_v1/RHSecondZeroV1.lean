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

import RHFirstZeroV1

/-!
# A second zero of `ζ` on the critical line, with `20.9 ≤ t ≤ 21.1`

The same checker as `RHFirstZeroV1` (`lamIv_mem`), with `M = 11`, `d = 18`, `K = 60`:
`re Λ(1/2 + 20.9i) ∈ [1.085337, 1.086279]·10⁻⁸` and `re Λ(1/2 + 21.1i) ∈ [−5.859899, −5.850487]·10⁻⁹`
(Arb: 1.0858080·10⁻⁸ and −5.8551929·10⁻⁹).  With `first_zero`, `ζ` has two distinct zeros on the line.
AUTHORITY_EFFECT = NONE.
-/

open Complex Set

namespace AEGIS.RHSecondZeroV1

open AEGIS.RHExpEnclosureV1 AEGIS.RHLambdaCheckV1 AEGIS.RHCriticalLineSignV1 AEGIS.RHFirstZeroV1

/-- The kernel evaluates the enclosure at `t = 20.9`: it lies above `0`. -/
theorem lam209_pos : 0 < (lamIv 128 (209 / 10) 11 18 60 22 6 30).lo := by decide +kernel

/-- The kernel evaluates the enclosure at `t = 21.1`: it lies below `0`. -/
theorem lam211_neg : (lamIv 128 (211 / 10) 11 18 60 22 6 30).hi < 0 := by decide +kernel

theorem Xi209_pos : 0 < (Xi (209 / 10)).re := by
  have h := (lamIv_mem 128 (209 / 10) 11 18 60 22 6 30 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [piHi]) (by norm_num)).1
  have hpos : 0 < ((lamIv 128 (209 / 10) 11 18 60 22 6 30).lo : ℝ) / 2 ^ 128 :=
    div_pos (by exact_mod_cast lam209_pos) (by positivity)
  have e : ((209 / 10 : ℚ) : ℝ) = 209 / 10 := by norm_num
  rw [e] at h
  linarith

theorem Xi211_neg : (Xi (211 / 10)).re < 0 := by
  have h := (lamIv_mem 128 (211 / 10) 11 18 60 22 6 30 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [piHi]) (by norm_num)).2
  have hneg : ((lamIv 128 (211 / 10) 11 18 60 22 6 30).hi : ℝ) / 2 ^ 128 < 0 :=
    div_neg_of_neg_of_pos (by exact_mod_cast lam211_neg) (by positivity)
  have e : ((211 / 10 : ℚ) : ℝ) = 211 / 10 := by norm_num
  rw [e] at h
  linarith

/-- **A zero of `ζ` on the critical line with `20.9 ≤ t ≤ 21.1`.** -/
theorem second_zero : ∃ t ∈ Set.Icc (209 / 10 : ℝ) (211 / 10), riemannZeta (1 / 2 + t * I) = 0 :=
  exists_zero_of_sign_change (by norm_num) (Or.inr ⟨Xi209_pos.le, Xi211_neg.le⟩)

/-- **Two distinct zeros of `ζ` on the critical line.** -/
theorem two_zeros : ∃ t₁ t₂ : ℝ, 14 ≤ t₁ ∧ t₁ < t₂ ∧ t₂ ≤ 211 / 10 ∧
    riemannZeta (1 / 2 + t₁ * I) = 0 ∧ riemannZeta (1 / 2 + t₂ * I) = 0 := by
  obtain ⟨t₁, ⟨h1, h1'⟩, z1⟩ := first_zero
  obtain ⟨t₂, ⟨h2, h2'⟩, z2⟩ := second_zero
  exact ⟨t₁, t₂, h1, by linarith, h2', z1, z2⟩

end AEGIS.RHSecondZeroV1

#print axioms AEGIS.RHSecondZeroV1.second_zero
#print axioms AEGIS.RHSecondZeroV1.two_zeros
