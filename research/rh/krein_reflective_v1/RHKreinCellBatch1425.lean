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

/-! Serialized cells 1425 to 1434: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1425 : List ℚ := [18825/256]
def b1426 : List ℚ := [4725/64]
def b1427 : List ℚ := [18975/256]
def b1428 : List ℚ := [38025/512, 9525/128]
def b1429 : List ℚ := [38175/512, 19125/256]
def b1430 : List ℚ := [75]
def b1431 : List ℚ := [19275/256]
def b1432 : List ℚ := [9675/128]
def b1433 : List ℚ := [19425/256]
def b1434 : List ℚ := [4875/64]

def breaks1425 : List (List ℚ) := [b1425, b1426, b1427, b1428, b1429, b1430, b1431, b1432, b1433, b1434]

theorem c1425 : checkCell pa19 (cellAt 1425) b1425 = true := by decide +kernel

theorem c1426 : checkCell pa19 (cellAt 1426) b1426 = true := by decide +kernel

theorem c1427 : checkCell pa19 (cellAt 1427) b1427 = true := by decide +kernel

theorem c1428 : checkCell pa19 (cellAt 1428) b1428 = true := by decide +kernel

theorem c1429 : checkCell pa19 (cellAt 1429) b1429 = true := by decide +kernel

theorem c1430 : checkCell pa19 (cellAt 1430) b1430 = true := by decide +kernel

theorem c1431 : checkCell pa19 (cellAt 1431) b1431 = true := by decide +kernel

theorem c1432 : checkCell pa19 (cellAt 1432) b1432 = true := by decide +kernel

theorem c1433 : checkCell pa19 (cellAt 1433) b1433 = true := by decide +kernel

theorem c1434 : checkCell pa19 (cellAt 1434) b1434 = true := by decide +kernel

theorem slice1425 : slice 1425 10 = [cellAt 1425, cellAt 1426, cellAt 1427, cellAt 1428, cellAt 1429, cellAt 1430, cellAt 1431, cellAt 1432, cellAt 1433, cellAt 1434] := by decide +kernel

theorem batch1425_ok : checkAll pa19 (slice 1425 10) breaks1425 = true := by
  rw [slice1425]
  simp only [breaks1425, checkAll, c1425, c1426, c1427, c1428, c1429, c1430, c1431, c1432, c1433, c1434, Bool.and_self]

theorem batch1425 : ∀ c ∈ slice 1425 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1425_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1425
