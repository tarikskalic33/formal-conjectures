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

/-! Serialized cells 1605 to 1614: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1605 : List ℚ := [64575/512, 32325/256]
def b1606 : List ℚ := [64725/512, 2025/16]
def b1607 : List ℚ := [64875/512, 32475/256]
def b1608 : List ℚ := [16275/128]
def b1609 : List ℚ := [32625/256]
def b1610 : List ℚ := [8175/64]
def b1611 : List ℚ := [32775/256]
def b1612 : List ℚ := [16425/128]
def b1613 : List ℚ := [65775/512, 32925/256]
def b1614 : List ℚ := [65925/512, 4125/32]

def breaks1605 : List (List ℚ) := [b1605, b1606, b1607, b1608, b1609, b1610, b1611, b1612, b1613, b1614]

theorem c1605 : checkCell pa19 (cellAt 1605) b1605 = true := by decide +kernel

theorem c1606 : checkCell pa19 (cellAt 1606) b1606 = true := by decide +kernel

theorem c1607 : checkCell pa19 (cellAt 1607) b1607 = true := by decide +kernel

theorem c1608 : checkCell pa19 (cellAt 1608) b1608 = true := by decide +kernel

theorem c1609 : checkCell pa19 (cellAt 1609) b1609 = true := by decide +kernel

theorem c1610 : checkCell pa19 (cellAt 1610) b1610 = true := by decide +kernel

theorem c1611 : checkCell pa19 (cellAt 1611) b1611 = true := by decide +kernel

theorem c1612 : checkCell pa19 (cellAt 1612) b1612 = true := by decide +kernel

theorem c1613 : checkCell pa19 (cellAt 1613) b1613 = true := by decide +kernel

theorem c1614 : checkCell pa19 (cellAt 1614) b1614 = true := by decide +kernel

theorem slice1605 : slice 1605 10 = [cellAt 1605, cellAt 1606, cellAt 1607, cellAt 1608, cellAt 1609, cellAt 1610, cellAt 1611, cellAt 1612, cellAt 1613, cellAt 1614] := by decide +kernel

theorem batch1605_ok : checkAll pa19 (slice 1605 10) breaks1605 = true := by
  rw [slice1605]
  simp only [breaks1605, checkAll, c1605, c1606, c1607, c1608, c1609, c1610, c1611, c1612, c1613, c1614, Bool.and_self]

theorem batch1605 : ∀ c ∈ slice 1605 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1605_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1605
