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

/-! Serialized cells 1585 to 1594: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1585 : List ℚ := [30825/256]
def b1586 : List ℚ := [7725/64]
def b1587 : List ℚ := [30975/256]
def b1588 : List ℚ := [15525/128]
def b1589 : List ℚ := [31125/256]
def b1590 : List ℚ := [975/8]
def b1591 : List ℚ := [31275/256]
def b1592 : List ℚ := [15675/128]
def b1593 : List ℚ := [31425/256]
def b1594 : List ℚ := [7875/64]

def breaks1585 : List (List ℚ) := [b1585, b1586, b1587, b1588, b1589, b1590, b1591, b1592, b1593, b1594]

theorem c1585 : checkCell pa19 (cellAt 1585) b1585 = true := by decide +kernel

theorem c1586 : checkCell pa19 (cellAt 1586) b1586 = true := by decide +kernel

theorem c1587 : checkCell pa19 (cellAt 1587) b1587 = true := by decide +kernel

theorem c1588 : checkCell pa19 (cellAt 1588) b1588 = true := by decide +kernel

theorem c1589 : checkCell pa19 (cellAt 1589) b1589 = true := by decide +kernel

theorem c1590 : checkCell pa19 (cellAt 1590) b1590 = true := by decide +kernel

theorem c1591 : checkCell pa19 (cellAt 1591) b1591 = true := by decide +kernel

theorem c1592 : checkCell pa19 (cellAt 1592) b1592 = true := by decide +kernel

theorem c1593 : checkCell pa19 (cellAt 1593) b1593 = true := by decide +kernel

theorem c1594 : checkCell pa19 (cellAt 1594) b1594 = true := by decide +kernel

theorem slice1585 : slice 1585 10 = [cellAt 1585, cellAt 1586, cellAt 1587, cellAt 1588, cellAt 1589, cellAt 1590, cellAt 1591, cellAt 1592, cellAt 1593, cellAt 1594] := by decide +kernel

theorem batch1585_ok : checkAll pa19 (slice 1585 10) breaks1585 = true := by
  rw [slice1585]
  simp only [breaks1585, checkAll, c1585, c1586, c1587, c1588, c1589, c1590, c1591, c1592, c1593, c1594, Bool.and_self]

theorem batch1585 : ∀ c ∈ slice 1585 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1585_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1585
