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

/-! Serialized cells 425 to 434: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0425 : List ℚ := [33375/32768]
def b0426 : List ℚ := [16725/16384]
def b0427 : List ℚ := [33525/32768]
def b0428 : List ℚ := [525/512]
def b0429 : List ℚ := [33675/32768]
def b0430 : List ℚ := [16875/16384]
def b0431 : List ℚ := [33825/32768]
def b0432 : List ℚ := [8475/8192]
def b0433 : List ℚ := [33975/32768]
def b0434 : List ℚ := [17025/16384]

def breaks0425 : List (List ℚ) := [b0425, b0426, b0427, b0428, b0429, b0430, b0431, b0432, b0433, b0434]

theorem c0425 : checkCell pa19 (cellAt 425) b0425 = true := by decide +kernel

theorem c0426 : checkCell pa19 (cellAt 426) b0426 = true := by decide +kernel

theorem c0427 : checkCell pa19 (cellAt 427) b0427 = true := by decide +kernel

theorem c0428 : checkCell pa19 (cellAt 428) b0428 = true := by decide +kernel

theorem c0429 : checkCell pa19 (cellAt 429) b0429 = true := by decide +kernel

theorem c0430 : checkCell pa19 (cellAt 430) b0430 = true := by decide +kernel

theorem c0431 : checkCell pa19 (cellAt 431) b0431 = true := by decide +kernel

theorem c0432 : checkCell pa19 (cellAt 432) b0432 = true := by decide +kernel

theorem c0433 : checkCell pa19 (cellAt 433) b0433 = true := by decide +kernel

theorem c0434 : checkCell pa19 (cellAt 434) b0434 = true := by decide +kernel

theorem slice0425 : slice 425 10 = [cellAt 425, cellAt 426, cellAt 427, cellAt 428, cellAt 429, cellAt 430, cellAt 431, cellAt 432, cellAt 433, cellAt 434] := by decide +kernel

theorem batch0425_ok : checkAll pa19 (slice 425 10) breaks0425 = true := by
  rw [slice0425]
  simp only [breaks0425, checkAll, c0425, c0426, c0427, c0428, c0429, c0430, c0431, c0432, c0433, c0434, Bool.and_self]

theorem batch0425 : ∀ c ∈ slice 425 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0425_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0425
