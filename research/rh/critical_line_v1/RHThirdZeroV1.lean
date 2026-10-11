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

import RHSecondZeroV1

/-!
# A third zero of `ζ` on the critical line, with `24.9 ≤ t ≤ 25.1`

The same checker (`lamIv_mem`) with `π` to forty digits, `M = 13`, `d = 22`, `K = 70`:
`re Λ(1/2 + 24.9i) ∈ [−4.82157, −4.82061]·10⁻¹⁰` and `re Λ(1/2 + 25.1i) ∈ [3.39414, 3.39510]·10⁻¹⁰`
(Arb: −4.8210895·10⁻¹⁰ and 3.3946199·10⁻¹⁰).  With `two_zeros`, `ζ` has three distinct zeros on the
line.  AUTHORITY_EFFECT = NONE.
-/

open Complex Set

namespace AEGIS.RHThirdZeroV1

open AEGIS.RHExpEnclosureV1 AEGIS.RHLambdaCheckV1 AEGIS.RHCriticalLineSignV1 AEGIS.RHFirstZeroV1
  AEGIS.RHSecondZeroV1

/-- The kernel evaluates the enclosure at `t = 24.9`: it lies below `0`. -/
theorem lam249_neg : (lamIv 128 (249 / 10) 13 22 70 22 6 30).hi < 0 := by decide +kernel

/-- The kernel evaluates the enclosure at `t = 25.1`: it lies above `0`. -/
theorem lam251_pos : 0 < (lamIv 128 (251 / 10) 13 22 70 22 6 30).lo := by decide +kernel

theorem Xi249_neg : (Xi (249 / 10)).re < 0 := by
  have h := (lamIv_mem 128 (249 / 10) 13 22 70 22 6 30 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [piHi]) (by norm_num)).2
  have hneg : ((lamIv 128 (249 / 10) 13 22 70 22 6 30).hi : ℝ) / 2 ^ 128 < 0 :=
    div_neg_of_neg_of_pos (by exact_mod_cast lam249_neg) (by positivity)
  have e : ((249 / 10 : ℚ) : ℝ) = 249 / 10 := by norm_num
  rw [e] at h
  linarith

theorem Xi251_pos : 0 < (Xi (251 / 10)).re := by
  have h := (lamIv_mem 128 (251 / 10) 13 22 70 22 6 30 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [piHi]) (by norm_num)).1
  have hpos : 0 < ((lamIv 128 (251 / 10) 13 22 70 22 6 30).lo : ℝ) / 2 ^ 128 :=
    div_pos (by exact_mod_cast lam251_pos) (by positivity)
  have e : ((251 / 10 : ℚ) : ℝ) = 251 / 10 := by norm_num
  rw [e] at h
  linarith

/-- **A zero of `ζ` on the critical line with `24.9 ≤ t ≤ 25.1`.** -/
theorem third_zero : ∃ t ∈ Set.Icc (249 / 10 : ℝ) (251 / 10), riemannZeta (1 / 2 + t * I) = 0 :=
  exists_zero_of_sign_change (by norm_num) (Or.inl ⟨Xi249_neg.le, Xi251_pos.le⟩)

/-- **Three distinct zeros of `ζ` on the critical line.** -/
theorem three_zeros : ∃ t₁ t₂ t₃ : ℝ, 14 ≤ t₁ ∧ t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ ≤ 251 / 10 ∧
    riemannZeta (1 / 2 + t₁ * I) = 0 ∧ riemannZeta (1 / 2 + t₂ * I) = 0 ∧
    riemannZeta (1 / 2 + t₃ * I) = 0 := by
  obtain ⟨t₁, ⟨h1, h1'⟩, z1⟩ := first_zero
  obtain ⟨t₂, ⟨h2, h2'⟩, z2⟩ := second_zero
  obtain ⟨t₃, ⟨h3, h3'⟩, z3⟩ := third_zero
  exact ⟨t₁, t₂, t₃, h1, by linarith, by linarith, h3', z1, z2, z3⟩

end AEGIS.RHThirdZeroV1

#print axioms AEGIS.RHThirdZeroV1.third_zero
#print axioms AEGIS.RHThirdZeroV1.three_zeros
