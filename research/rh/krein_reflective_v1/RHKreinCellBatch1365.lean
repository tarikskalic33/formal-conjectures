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

/-! Serialized cells 1365 to 1374: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1365 : List ℚ := [14325/256]
def b1366 : List ℚ := [225/4]
def b1367 : List ℚ := [14475/256]
def b1368 : List ℚ := [7275/128]
def b1369 : List ℚ := [14625/256]
def b1370 : List ℚ := [3675/64]
def b1371 : List ℚ := [14775/256]
def b1372 : List ℚ := [7425/128]
def b1373 : List ℚ := [14925/256]
def b1374 : List ℚ := [1875/32]

def breaks1365 : List (List ℚ) := [b1365, b1366, b1367, b1368, b1369, b1370, b1371, b1372, b1373, b1374]

theorem c1365 : checkCell pa19 (cellAt 1365) b1365 = true := by decide +kernel

theorem c1366 : checkCell pa19 (cellAt 1366) b1366 = true := by decide +kernel

theorem c1367 : checkCell pa19 (cellAt 1367) b1367 = true := by decide +kernel

theorem c1368 : checkCell pa19 (cellAt 1368) b1368 = true := by decide +kernel

theorem c1369 : checkCell pa19 (cellAt 1369) b1369 = true := by decide +kernel

theorem c1370 : checkCell pa19 (cellAt 1370) b1370 = true := by decide +kernel

theorem c1371 : checkCell pa19 (cellAt 1371) b1371 = true := by decide +kernel

theorem c1372 : checkCell pa19 (cellAt 1372) b1372 = true := by decide +kernel

theorem c1373 : checkCell pa19 (cellAt 1373) b1373 = true := by decide +kernel

theorem c1374 : checkCell pa19 (cellAt 1374) b1374 = true := by decide +kernel

theorem slice1365 : slice 1365 10 = [cellAt 1365, cellAt 1366, cellAt 1367, cellAt 1368, cellAt 1369, cellAt 1370, cellAt 1371, cellAt 1372, cellAt 1373, cellAt 1374] := by decide +kernel

theorem batch1365_ok : checkAll pa19 (slice 1365 10) breaks1365 = true := by
  rw [slice1365]
  simp only [breaks1365, checkAll, c1365, c1366, c1367, c1368, c1369, c1370, c1371, c1372, c1373, c1374, Bool.and_self]

theorem batch1365 : ∀ c ∈ slice 1365 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1365_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1365
