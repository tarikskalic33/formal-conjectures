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

/-! Serialized cells 1375 to 1384: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1375 : List ℚ := [15075/256]
def b1376 : List ℚ := [7575/128]
def b1377 : List ℚ := [15225/256]
def b1378 : List ℚ := [3825/64]
def b1379 : List ℚ := [15375/256]
def b1380 : List ℚ := [7725/128]
def b1381 : List ℚ := [15525/256]
def b1382 : List ℚ := [975/16]
def b1383 : List ℚ := [15675/256]
def b1384 : List ℚ := [7875/128]

def breaks1375 : List (List ℚ) := [b1375, b1376, b1377, b1378, b1379, b1380, b1381, b1382, b1383, b1384]

theorem c1375 : checkCell pa19 (cellAt 1375) b1375 = true := by decide +kernel

theorem c1376 : checkCell pa19 (cellAt 1376) b1376 = true := by decide +kernel

theorem c1377 : checkCell pa19 (cellAt 1377) b1377 = true := by decide +kernel

theorem c1378 : checkCell pa19 (cellAt 1378) b1378 = true := by decide +kernel

theorem c1379 : checkCell pa19 (cellAt 1379) b1379 = true := by decide +kernel

theorem c1380 : checkCell pa19 (cellAt 1380) b1380 = true := by decide +kernel

theorem c1381 : checkCell pa19 (cellAt 1381) b1381 = true := by decide +kernel

theorem c1382 : checkCell pa19 (cellAt 1382) b1382 = true := by decide +kernel

theorem c1383 : checkCell pa19 (cellAt 1383) b1383 = true := by decide +kernel

theorem c1384 : checkCell pa19 (cellAt 1384) b1384 = true := by decide +kernel

theorem slice1375 : slice 1375 10 = [cellAt 1375, cellAt 1376, cellAt 1377, cellAt 1378, cellAt 1379, cellAt 1380, cellAt 1381, cellAt 1382, cellAt 1383, cellAt 1384] := by decide +kernel

theorem batch1375_ok : checkAll pa19 (slice 1375 10) breaks1375 = true := by
  rw [slice1375]
  simp only [breaks1375, checkAll, c1375, c1376, c1377, c1378, c1379, c1380, c1381, c1382, c1383, c1384, Bool.and_self]

theorem batch1375 : ∀ c ∈ slice 1375 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1375_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1375
