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

/-! Serialized cells 1575 to 1584: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1575 : List ℚ := [30075/256]
def b1576 : List ℚ := [15075/128]
def b1577 : List ℚ := [30225/256]
def b1578 : List ℚ := [7575/64]
def b1579 : List ℚ := [30375/256]
def b1580 : List ℚ := [15225/128]
def b1581 : List ℚ := [30525/256]
def b1582 : List ℚ := [3825/32]
def b1583 : List ℚ := [30675/256]
def b1584 : List ℚ := [15375/128]

def breaks1575 : List (List ℚ) := [b1575, b1576, b1577, b1578, b1579, b1580, b1581, b1582, b1583, b1584]

theorem c1575 : checkCell pa19 (cellAt 1575) b1575 = true := by decide +kernel

theorem c1576 : checkCell pa19 (cellAt 1576) b1576 = true := by decide +kernel

theorem c1577 : checkCell pa19 (cellAt 1577) b1577 = true := by decide +kernel

theorem c1578 : checkCell pa19 (cellAt 1578) b1578 = true := by decide +kernel

theorem c1579 : checkCell pa19 (cellAt 1579) b1579 = true := by decide +kernel

theorem c1580 : checkCell pa19 (cellAt 1580) b1580 = true := by decide +kernel

theorem c1581 : checkCell pa19 (cellAt 1581) b1581 = true := by decide +kernel

theorem c1582 : checkCell pa19 (cellAt 1582) b1582 = true := by decide +kernel

theorem c1583 : checkCell pa19 (cellAt 1583) b1583 = true := by decide +kernel

theorem c1584 : checkCell pa19 (cellAt 1584) b1584 = true := by decide +kernel

theorem slice1575 : slice 1575 10 = [cellAt 1575, cellAt 1576, cellAt 1577, cellAt 1578, cellAt 1579, cellAt 1580, cellAt 1581, cellAt 1582, cellAt 1583, cellAt 1584] := by decide +kernel

theorem batch1575_ok : checkAll pa19 (slice 1575 10) breaks1575 = true := by
  rw [slice1575]
  simp only [breaks1575, checkAll, c1575, c1576, c1577, c1578, c1579, c1580, c1581, c1582, c1583, c1584, Bool.and_self]

theorem batch1575 : ∀ c ∈ slice 1575 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1575_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1575
