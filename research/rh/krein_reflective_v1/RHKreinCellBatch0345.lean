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

/-! Serialized cells 345 to 354: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0345 : List ℚ := [27375/32768]
def b0346 : List ℚ := [13725/16384]
def b0347 : List ℚ := [27525/32768]
def b0348 : List ℚ := [1725/2048]
def b0349 : List ℚ := [27675/32768]
def b0350 : List ℚ := [13875/16384]
def b0351 : List ℚ := [27825/32768]
def b0352 : List ℚ := [6975/8192]
def b0353 : List ℚ := [27975/32768]
def b0354 : List ℚ := [14025/16384]

def breaks0345 : List (List ℚ) := [b0345, b0346, b0347, b0348, b0349, b0350, b0351, b0352, b0353, b0354]

theorem c0345 : checkCell pa19 (cellAt 345) b0345 = true := by decide +kernel

theorem c0346 : checkCell pa19 (cellAt 346) b0346 = true := by decide +kernel

theorem c0347 : checkCell pa19 (cellAt 347) b0347 = true := by decide +kernel

theorem c0348 : checkCell pa19 (cellAt 348) b0348 = true := by decide +kernel

theorem c0349 : checkCell pa19 (cellAt 349) b0349 = true := by decide +kernel

theorem c0350 : checkCell pa19 (cellAt 350) b0350 = true := by decide +kernel

theorem c0351 : checkCell pa19 (cellAt 351) b0351 = true := by decide +kernel

theorem c0352 : checkCell pa19 (cellAt 352) b0352 = true := by decide +kernel

theorem c0353 : checkCell pa19 (cellAt 353) b0353 = true := by decide +kernel

theorem c0354 : checkCell pa19 (cellAt 354) b0354 = true := by decide +kernel

theorem slice0345 : slice 345 10 = [cellAt 345, cellAt 346, cellAt 347, cellAt 348, cellAt 349, cellAt 350, cellAt 351, cellAt 352, cellAt 353, cellAt 354] := by decide +kernel

theorem batch0345_ok : checkAll pa19 (slice 345 10) breaks0345 = true := by
  rw [slice0345]
  simp only [breaks0345, checkAll, c0345, c0346, c0347, c0348, c0349, c0350, c0351, c0352, c0353, c0354, Bool.and_self]

theorem batch0345 : ∀ c ∈ slice 345 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0345_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0345
