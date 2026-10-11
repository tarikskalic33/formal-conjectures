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

/-! Serialized cells 1395 to 1404: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1395 : List ℚ := [16575/256]
def b1396 : List ℚ := [8325/128]
def b1397 : List ℚ := [16725/256]
def b1398 : List ℚ := [525/8]
def b1399 : List ℚ := [16875/256]
def b1400 : List ℚ := [8475/128]
def b1401 : List ℚ := [17025/256]
def b1402 : List ℚ := [4275/64]
def b1403 : List ℚ := [17175/256]
def b1404 : List ℚ := [8625/128]

def breaks1395 : List (List ℚ) := [b1395, b1396, b1397, b1398, b1399, b1400, b1401, b1402, b1403, b1404]

theorem c1395 : checkCell pa19 (cellAt 1395) b1395 = true := by decide +kernel

theorem c1396 : checkCell pa19 (cellAt 1396) b1396 = true := by decide +kernel

theorem c1397 : checkCell pa19 (cellAt 1397) b1397 = true := by decide +kernel

theorem c1398 : checkCell pa19 (cellAt 1398) b1398 = true := by decide +kernel

theorem c1399 : checkCell pa19 (cellAt 1399) b1399 = true := by decide +kernel

theorem c1400 : checkCell pa19 (cellAt 1400) b1400 = true := by decide +kernel

theorem c1401 : checkCell pa19 (cellAt 1401) b1401 = true := by decide +kernel

theorem c1402 : checkCell pa19 (cellAt 1402) b1402 = true := by decide +kernel

theorem c1403 : checkCell pa19 (cellAt 1403) b1403 = true := by decide +kernel

theorem c1404 : checkCell pa19 (cellAt 1404) b1404 = true := by decide +kernel

theorem slice1395 : slice 1395 10 = [cellAt 1395, cellAt 1396, cellAt 1397, cellAt 1398, cellAt 1399, cellAt 1400, cellAt 1401, cellAt 1402, cellAt 1403, cellAt 1404] := by decide +kernel

theorem batch1395_ok : checkAll pa19 (slice 1395 10) breaks1395 = true := by
  rw [slice1395]
  simp only [breaks1395, checkAll, c1395, c1396, c1397, c1398, c1399, c1400, c1401, c1402, c1403, c1404, Bool.and_self]

theorem batch1395 : ∀ c ∈ slice 1395 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1395_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1395
