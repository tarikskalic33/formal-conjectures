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
# From a kernel check to the sign of `re Λ(1/2 + it)`, and zeros stay off the checked points

`xi_neg_of_check`, `xi_pos_of_check`: at `p = 192`, `M = 26`, `d = 36`, `K = 110`, `J = 22`, `s = 6`,
`N = 40` (valid for `t ≤ 51`), a kernel-checked sign of `lamIv` is the sign of `re Λ(1/2 + it)`.
`Xi_re_zero_of_zeta`: `ζ(1/2 + it) = 0 → re Λ(1/2 + it) = 0`, so a zero found in `[a, b]` is not at an
endpoint where `re Λ ≠ 0`.  AUTHORITY_EFFECT = NONE.
-/

open Complex

namespace AEGIS.RHXiSignV1

open AEGIS.RHExpEnclosureV1 AEGIS.RHLambdaCheckV1 AEGIS.RHCriticalLineSignV1 AEGIS.RHFirstZeroV1

theorem xi_neg_of_check {t : ℚ} (hzM : (-3 / 4 : ℚ) ^ 2 + (t / 2) ^ 2 ≤ 26 ^ 2)
    (h : (lamIv 192 t 26 36 110 22 6 40).hi < 0) : (Xi (t : ℝ)).re < 0 := by
  have hm := (lamIv_mem 192 t 26 36 110 22 6 40 (by norm_num) hzM (by norm_num) (by norm_num)
    (by norm_num [piHi]) (by norm_num)).2
  have hneg : ((lamIv 192 t 26 36 110 22 6 40).hi : ℝ) / 2 ^ 192 < 0 :=
    div_neg_of_neg_of_pos (by exact_mod_cast h) (by positivity)
  linarith

theorem xi_pos_of_check {t : ℚ} (hzM : (-3 / 4 : ℚ) ^ 2 + (t / 2) ^ 2 ≤ 26 ^ 2)
    (h : 0 < (lamIv 192 t 26 36 110 22 6 40).lo) : 0 < (Xi (t : ℝ)).re := by
  have hm := (lamIv_mem 192 t 26 36 110 22 6 40 (by norm_num) hzM (by norm_num) (by norm_num)
    (by norm_num [piHi]) (by norm_num)).1
  have hpos : 0 < ((lamIv 192 t 26 36 110 22 6 40).lo : ℝ) / 2 ^ 192 :=
    div_pos (by exact_mod_cast h) (by positivity)
  linarith

theorem Xi_re_zero_of_zeta {t : ℝ} (h : riemannZeta (1 / 2 + t * I) = 0) : (Xi t).re = 0 := by
  have hpos : 0 < (lineAt t).re := by rw [lineAt_re]; norm_num
  have hX : Xi t = 0 := by
    rw [Xi, completed_eq_mul hpos]
    show Gammaℝ (lineAt t) * riemannZeta (1 / 2 + t * I) = 0
    rw [h, mul_zero]
  rw [hX, zero_re]

theorem lt_of_zero_le {t b : ℝ} (ht : t ≤ b) (hz : riemannZeta (1 / 2 + t * I) = 0)
    (hb : (Xi b).re ≠ 0) : t < b :=
  lt_of_le_of_ne ht fun e => hb (e ▸ Xi_re_zero_of_zeta hz)

theorem lt_of_le_zero {t b : ℝ} (ht : b ≤ t) (hz : riemannZeta (1 / 2 + t * I) = 0)
    (hb : (Xi b).re ≠ 0) : b < t :=
  lt_of_le_of_ne ht fun e => hb (e ▸ Xi_re_zero_of_zeta hz)

end AEGIS.RHXiSignV1

#print axioms AEGIS.RHXiSignV1.xi_neg_of_check
#print axioms AEGIS.RHXiSignV1.Xi_re_zero_of_zeta
