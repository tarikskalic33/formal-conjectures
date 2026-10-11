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

/-! Serialized cells 1495 to 1504: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1495 : List ℚ := [24075/256]
def b1496 : List ℚ := [12075/128]
def b1497 : List ℚ := [24225/256]
def b1498 : List ℚ := [6075/64]
def b1499 : List ℚ := [24375/256]
def b1500 : List ℚ := [12225/128]
def b1501 : List ℚ := [24525/256]
def b1502 : List ℚ := [3075/32]
def b1503 : List ℚ := [24675/256]
def b1504 : List ℚ := [12375/128]

def breaks1495 : List (List ℚ) := [b1495, b1496, b1497, b1498, b1499, b1500, b1501, b1502, b1503, b1504]

theorem c1495 : checkCell pa19 (cellAt 1495) b1495 = true := by decide +kernel

theorem c1496 : checkCell pa19 (cellAt 1496) b1496 = true := by decide +kernel

theorem c1497 : checkCell pa19 (cellAt 1497) b1497 = true := by decide +kernel

theorem c1498 : checkCell pa19 (cellAt 1498) b1498 = true := by decide +kernel

theorem c1499 : checkCell pa19 (cellAt 1499) b1499 = true := by decide +kernel

theorem c1500 : checkCell pa19 (cellAt 1500) b1500 = true := by decide +kernel

theorem c1501 : checkCell pa19 (cellAt 1501) b1501 = true := by decide +kernel

theorem c1502 : checkCell pa19 (cellAt 1502) b1502 = true := by decide +kernel

theorem c1503 : checkCell pa19 (cellAt 1503) b1503 = true := by decide +kernel

theorem c1504 : checkCell pa19 (cellAt 1504) b1504 = true := by decide +kernel

theorem slice1495 : slice 1495 10 = [cellAt 1495, cellAt 1496, cellAt 1497, cellAt 1498, cellAt 1499, cellAt 1500, cellAt 1501, cellAt 1502, cellAt 1503, cellAt 1504] := by decide +kernel

theorem batch1495_ok : checkAll pa19 (slice 1495 10) breaks1495 = true := by
  rw [slice1495]
  simp only [breaks1495, checkAll, c1495, c1496, c1497, c1498, c1499, c1500, c1501, c1502, c1503, c1504, Bool.and_self]

theorem batch1495 : ∀ c ∈ slice 1495 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1495_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1495
