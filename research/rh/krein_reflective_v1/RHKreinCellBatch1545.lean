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

/-! Serialized cells 1545 to 1554: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1545 : List ℚ := [27825/256]
def b1546 : List ℚ := [6975/64]
def b1547 : List ℚ := [27975/256]
def b1548 : List ℚ := [14025/128]
def b1549 : List ℚ := [28125/256]
def b1550 : List ℚ := [3525/32]
def b1551 : List ℚ := [28275/256]
def b1552 : List ℚ := [14175/128]
def b1553 : List ℚ := [28425/256]
def b1554 : List ℚ := [7125/64]

def breaks1545 : List (List ℚ) := [b1545, b1546, b1547, b1548, b1549, b1550, b1551, b1552, b1553, b1554]

theorem c1545 : checkCell pa19 (cellAt 1545) b1545 = true := by decide +kernel

theorem c1546 : checkCell pa19 (cellAt 1546) b1546 = true := by decide +kernel

theorem c1547 : checkCell pa19 (cellAt 1547) b1547 = true := by decide +kernel

theorem c1548 : checkCell pa19 (cellAt 1548) b1548 = true := by decide +kernel

theorem c1549 : checkCell pa19 (cellAt 1549) b1549 = true := by decide +kernel

theorem c1550 : checkCell pa19 (cellAt 1550) b1550 = true := by decide +kernel

theorem c1551 : checkCell pa19 (cellAt 1551) b1551 = true := by decide +kernel

theorem c1552 : checkCell pa19 (cellAt 1552) b1552 = true := by decide +kernel

theorem c1553 : checkCell pa19 (cellAt 1553) b1553 = true := by decide +kernel

theorem c1554 : checkCell pa19 (cellAt 1554) b1554 = true := by decide +kernel

theorem slice1545 : slice 1545 10 = [cellAt 1545, cellAt 1546, cellAt 1547, cellAt 1548, cellAt 1549, cellAt 1550, cellAt 1551, cellAt 1552, cellAt 1553, cellAt 1554] := by decide +kernel

theorem batch1545_ok : checkAll pa19 (slice 1545 10) breaks1545 = true := by
  rw [slice1545]
  simp only [breaks1545, checkAll, c1545, c1546, c1547, c1548, c1549, c1550, c1551, c1552, c1553, c1554, Bool.and_self]

theorem batch1545 : ∀ c ∈ slice 1545 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1545_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1545
