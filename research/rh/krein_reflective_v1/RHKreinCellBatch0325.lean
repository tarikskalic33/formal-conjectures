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

/-! Serialized cells 325 to 334: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0325 : List ℚ := [25875/32768]
def b0326 : List ℚ := [12975/16384]
def b0327 : List ℚ := [26025/32768]
def b0328 : List ℚ := [6525/8192]
def b0329 : List ℚ := [26175/32768]
def b0330 : List ℚ := [13125/16384]
def b0331 : List ℚ := [26325/32768]
def b0332 : List ℚ := [825/1024]
def b0333 : List ℚ := [26475/32768]
def b0334 : List ℚ := [13275/16384]

def breaks0325 : List (List ℚ) := [b0325, b0326, b0327, b0328, b0329, b0330, b0331, b0332, b0333, b0334]

theorem c0325 : checkCell pa19 (cellAt 325) b0325 = true := by decide +kernel

theorem c0326 : checkCell pa19 (cellAt 326) b0326 = true := by decide +kernel

theorem c0327 : checkCell pa19 (cellAt 327) b0327 = true := by decide +kernel

theorem c0328 : checkCell pa19 (cellAt 328) b0328 = true := by decide +kernel

theorem c0329 : checkCell pa19 (cellAt 329) b0329 = true := by decide +kernel

theorem c0330 : checkCell pa19 (cellAt 330) b0330 = true := by decide +kernel

theorem c0331 : checkCell pa19 (cellAt 331) b0331 = true := by decide +kernel

theorem c0332 : checkCell pa19 (cellAt 332) b0332 = true := by decide +kernel

theorem c0333 : checkCell pa19 (cellAt 333) b0333 = true := by decide +kernel

theorem c0334 : checkCell pa19 (cellAt 334) b0334 = true := by decide +kernel

theorem slice0325 : slice 325 10 = [cellAt 325, cellAt 326, cellAt 327, cellAt 328, cellAt 329, cellAt 330, cellAt 331, cellAt 332, cellAt 333, cellAt 334] := by decide +kernel

theorem batch0325_ok : checkAll pa19 (slice 325 10) breaks0325 = true := by
  rw [slice0325]
  simp only [breaks0325, checkAll, c0325, c0326, c0327, c0328, c0329, c0330, c0331, c0332, c0333, c0334, Bool.and_self]

theorem batch0325 : ∀ c ∈ slice 325 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0325_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0325
