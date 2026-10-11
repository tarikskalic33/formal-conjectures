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

import RHKreinCellBatchV1

/-! Serialized cells 355 to 364: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0355 : List ℚ := [28125/32768]
def b0356 : List ℚ := [3525/4096]
def b0357 : List ℚ := [28275/32768]
def b0358 : List ℚ := [14175/16384]
def b0359 : List ℚ := [28425/32768]
def b0360 : List ℚ := [7125/8192]
def b0361 : List ℚ := [28575/32768]
def b0362 : List ℚ := [14325/16384]
def b0363 : List ℚ := [28725/32768]
def b0364 : List ℚ := [225/256]

def breaks0355 : List (List ℚ) := [b0355, b0356, b0357, b0358, b0359, b0360, b0361, b0362, b0363, b0364]

theorem c0355 : checkCell pa19 (cellAt 355) b0355 = true := by decide +kernel

theorem c0356 : checkCell pa19 (cellAt 356) b0356 = true := by decide +kernel

theorem c0357 : checkCell pa19 (cellAt 357) b0357 = true := by decide +kernel

theorem c0358 : checkCell pa19 (cellAt 358) b0358 = true := by decide +kernel

theorem c0359 : checkCell pa19 (cellAt 359) b0359 = true := by decide +kernel

theorem c0360 : checkCell pa19 (cellAt 360) b0360 = true := by decide +kernel

theorem c0361 : checkCell pa19 (cellAt 361) b0361 = true := by decide +kernel

theorem c0362 : checkCell pa19 (cellAt 362) b0362 = true := by decide +kernel

theorem c0363 : checkCell pa19 (cellAt 363) b0363 = true := by decide +kernel

theorem c0364 : checkCell pa19 (cellAt 364) b0364 = true := by decide +kernel

theorem slice0355 : slice 355 10 = [cellAt 355, cellAt 356, cellAt 357, cellAt 358, cellAt 359, cellAt 360, cellAt 361, cellAt 362, cellAt 363, cellAt 364] := by decide +kernel

theorem batch0355_ok : checkAll pa19 (slice 355 10) breaks0355 = true := by
  rw [slice0355]
  simp only [breaks0355, checkAll, c0355, c0356, c0357, c0358, c0359, c0360, c0361, c0362, c0363, c0364, Bool.and_self]

theorem batch0355 : ∀ c ∈ slice 355 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0355_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0355
