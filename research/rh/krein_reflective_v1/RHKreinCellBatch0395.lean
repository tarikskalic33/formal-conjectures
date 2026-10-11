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

/-! Serialized cells 395 to 404: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0395 : List ℚ := [31125/32768]
def b0396 : List ℚ := [975/1024]
def b0397 : List ℚ := [31275/32768]
def b0398 : List ℚ := [15675/16384]
def b0399 : List ℚ := [31425/32768]
def b0400 : List ℚ := [7875/8192]
def b0401 : List ℚ := [31575/32768]
def b0402 : List ℚ := [15825/16384]
def b0403 : List ℚ := [31725/32768]
def b0404 : List ℚ := [3975/4096]

def breaks0395 : List (List ℚ) := [b0395, b0396, b0397, b0398, b0399, b0400, b0401, b0402, b0403, b0404]

theorem c0395 : checkCell pa19 (cellAt 395) b0395 = true := by decide +kernel

theorem c0396 : checkCell pa19 (cellAt 396) b0396 = true := by decide +kernel

theorem c0397 : checkCell pa19 (cellAt 397) b0397 = true := by decide +kernel

theorem c0398 : checkCell pa19 (cellAt 398) b0398 = true := by decide +kernel

theorem c0399 : checkCell pa19 (cellAt 399) b0399 = true := by decide +kernel

theorem c0400 : checkCell pa19 (cellAt 400) b0400 = true := by decide +kernel

theorem c0401 : checkCell pa19 (cellAt 401) b0401 = true := by decide +kernel

theorem c0402 : checkCell pa19 (cellAt 402) b0402 = true := by decide +kernel

theorem c0403 : checkCell pa19 (cellAt 403) b0403 = true := by decide +kernel

theorem c0404 : checkCell pa19 (cellAt 404) b0404 = true := by decide +kernel

theorem slice0395 : slice 395 10 = [cellAt 395, cellAt 396, cellAt 397, cellAt 398, cellAt 399, cellAt 400, cellAt 401, cellAt 402, cellAt 403, cellAt 404] := by decide +kernel

theorem batch0395_ok : checkAll pa19 (slice 395 10) breaks0395 = true := by
  rw [slice0395]
  simp only [breaks0395, checkAll, c0395, c0396, c0397, c0398, c0399, c0400, c0401, c0402, c0403, c0404, Bool.and_self]

theorem batch0395 : ∀ c ∈ slice 395 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0395_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0395
