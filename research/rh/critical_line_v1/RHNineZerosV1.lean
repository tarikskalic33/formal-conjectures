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

import RHThirdZeroV1
import RHZeroChecksAV1
import RHZeroChecksBV1
import RHZeroChecksCV1

/-!
# Nine zeros of `ζ` on the critical line with `14 ≤ t ≤ 48.9`

Signs of `re Λ(1/2 + it)`, each kernel-checked: `14 (−)`, `14.3 (+)`, `20.9 (+)`, `21.1 (−)`, `24.9 (−)`,
`25.1 (+)`, `31.7 (−)`, `35.3 (+)`, `39.3 (−)`, `42.2 (+)`, `45.7 (−)`, `48.9 (+)`.  Each sign change gives a
zero on the line; a zero is never at a checked point (`Xi_re_zero_of_zeta`), so the nine are distinct.
Numerically they are the zeros at t ≈ 14.13, 21.02, 25.01, 30.42, 32.94, 37.59, 40.92, 43.33, 48.01.

This verifies nine zeros; it says nothing about zeros off the line.  AUTHORITY_EFFECT = NONE.
-/

open Complex Set

namespace AEGIS.RHNineZerosV1

open AEGIS.RHCriticalLineSignV1 AEGIS.RHFirstZeroV1 AEGIS.RHSecondZeroV1 AEGIS.RHThirdZeroV1
  AEGIS.RHXiSignV1

theorem zero4 : ∃ t ∈ Icc (251 / 10 : ℝ) (317 / 10), riemannZeta (1 / 2 + t * I) = 0 :=
  exists_zero_of_sign_change (by norm_num) (Or.inr ⟨Xi251_pos.le, AEGIS.RHZeroChecksAV1.xi_a.le⟩)

theorem zero5 : ∃ t ∈ Icc (317 / 10 : ℝ) (353 / 10), riemannZeta (1 / 2 + t * I) = 0 :=
  exists_zero_of_sign_change (by norm_num)
    (Or.inl ⟨AEGIS.RHZeroChecksAV1.xi_a.le, AEGIS.RHZeroChecksAV1.xi_b.le⟩)

theorem zero6 : ∃ t ∈ Icc (353 / 10 : ℝ) (393 / 10), riemannZeta (1 / 2 + t * I) = 0 :=
  exists_zero_of_sign_change (by norm_num)
    (Or.inr ⟨AEGIS.RHZeroChecksAV1.xi_b.le, AEGIS.RHZeroChecksBV1.xi_a.le⟩)

theorem zero7 : ∃ t ∈ Icc (393 / 10 : ℝ) (422 / 10), riemannZeta (1 / 2 + t * I) = 0 :=
  exists_zero_of_sign_change (by norm_num)
    (Or.inl ⟨AEGIS.RHZeroChecksBV1.xi_a.le, AEGIS.RHZeroChecksBV1.xi_b.le⟩)

theorem zero8 : ∃ t ∈ Icc (422 / 10 : ℝ) (457 / 10), riemannZeta (1 / 2 + t * I) = 0 :=
  exists_zero_of_sign_change (by norm_num)
    (Or.inr ⟨AEGIS.RHZeroChecksBV1.xi_b.le, AEGIS.RHZeroChecksCV1.xi_a.le⟩)

theorem zero9 : ∃ t ∈ Icc (457 / 10 : ℝ) (489 / 10), riemannZeta (1 / 2 + t * I) = 0 :=
  exists_zero_of_sign_change (by norm_num)
    (Or.inl ⟨AEGIS.RHZeroChecksCV1.xi_a.le, AEGIS.RHZeroChecksCV1.xi_b.le⟩)

/-- **Nine distinct zeros of `ζ` on the critical line, `14 ≤ t₁ < ⋯ < t₉ ≤ 48.9`.** -/
theorem nine_zeros : ∃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ : ℝ,
    14 ≤ t₁ ∧ t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ < t₄ ∧ t₄ < t₅ ∧ t₅ < t₆ ∧ t₆ < t₇ ∧ t₇ < t₈ ∧ t₈ < t₉ ∧
    t₉ ≤ 489 / 10 ∧
    riemannZeta (1 / 2 + t₁ * I) = 0 ∧ riemannZeta (1 / 2 + t₂ * I) = 0 ∧
    riemannZeta (1 / 2 + t₃ * I) = 0 ∧ riemannZeta (1 / 2 + t₄ * I) = 0 ∧
    riemannZeta (1 / 2 + t₅ * I) = 0 ∧ riemannZeta (1 / 2 + t₆ * I) = 0 ∧
    riemannZeta (1 / 2 + t₇ * I) = 0 ∧ riemannZeta (1 / 2 + t₈ * I) = 0 ∧
    riemannZeta (1 / 2 + t₉ * I) = 0 := by
  obtain ⟨t1, ⟨a1, b1⟩, z1⟩ := first_zero
  obtain ⟨t2, ⟨a2, b2⟩, z2⟩ := second_zero
  obtain ⟨t3, ⟨a3, b3⟩, z3⟩ := third_zero
  obtain ⟨t4, ⟨a4, b4⟩, z4⟩ := zero4
  obtain ⟨t5, ⟨a5, b5⟩, z5⟩ := zero5
  obtain ⟨t6, ⟨a6, b6⟩, z6⟩ := zero6
  obtain ⟨t7, ⟨a7, b7⟩, z7⟩ := zero7
  obtain ⟨t8, ⟨a8, b8⟩, z8⟩ := zero8
  obtain ⟨t9, ⟨a9, b9⟩, z9⟩ := zero9
  have c3 := lt_of_zero_le b3 z3 Xi251_pos.ne'
  have c4 := lt_of_zero_le b4 z4 AEGIS.RHZeroChecksAV1.xi_a.ne
  have c5 := lt_of_zero_le b5 z5 AEGIS.RHZeroChecksAV1.xi_b.ne'
  have c6 := lt_of_zero_le b6 z6 AEGIS.RHZeroChecksBV1.xi_a.ne
  have c7 := lt_of_zero_le b7 z7 AEGIS.RHZeroChecksBV1.xi_b.ne'
  have c8 := lt_of_zero_le b8 z8 AEGIS.RHZeroChecksCV1.xi_a.ne
  exact ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, a1, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, b9, z1, z2, z3, z4, z5, z6, z7, z8, z9⟩

end AEGIS.RHNineZerosV1

#print axioms AEGIS.RHNineZerosV1.nine_zeros
