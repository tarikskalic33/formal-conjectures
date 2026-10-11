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

/-! Serialized cells 1435 to 1444: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1435 : List ℚ := [19575/256]
def b1436 : List ℚ := [9825/128]
def b1437 : List ℚ := [19725/256]
def b1438 : List ℚ := [2475/32]
def b1439 : List ℚ := [19875/256]
def b1440 : List ℚ := [9975/128]
def b1441 : List ℚ := [20025/256]
def b1442 : List ℚ := [5025/64]
def b1443 : List ℚ := [20175/256]
def b1444 : List ℚ := [10125/128]

def breaks1435 : List (List ℚ) := [b1435, b1436, b1437, b1438, b1439, b1440, b1441, b1442, b1443, b1444]

theorem c1435 : checkCell pa19 (cellAt 1435) b1435 = true := by decide +kernel

theorem c1436 : checkCell pa19 (cellAt 1436) b1436 = true := by decide +kernel

theorem c1437 : checkCell pa19 (cellAt 1437) b1437 = true := by decide +kernel

theorem c1438 : checkCell pa19 (cellAt 1438) b1438 = true := by decide +kernel

theorem c1439 : checkCell pa19 (cellAt 1439) b1439 = true := by decide +kernel

theorem c1440 : checkCell pa19 (cellAt 1440) b1440 = true := by decide +kernel

theorem c1441 : checkCell pa19 (cellAt 1441) b1441 = true := by decide +kernel

theorem c1442 : checkCell pa19 (cellAt 1442) b1442 = true := by decide +kernel

theorem c1443 : checkCell pa19 (cellAt 1443) b1443 = true := by decide +kernel

theorem c1444 : checkCell pa19 (cellAt 1444) b1444 = true := by decide +kernel

theorem slice1435 : slice 1435 10 = [cellAt 1435, cellAt 1436, cellAt 1437, cellAt 1438, cellAt 1439, cellAt 1440, cellAt 1441, cellAt 1442, cellAt 1443, cellAt 1444] := by decide +kernel

theorem batch1435_ok : checkAll pa19 (slice 1435 10) breaks1435 = true := by
  rw [slice1435]
  simp only [breaks1435, checkAll, c1435, c1436, c1437, c1438, c1439, c1440, c1441, c1442, c1443, c1444, Bool.and_self]

theorem batch1435 : ∀ c ∈ slice 1435 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1435_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1435
