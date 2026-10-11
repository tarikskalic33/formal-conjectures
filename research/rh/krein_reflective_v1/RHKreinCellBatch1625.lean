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

/-! Serialized cells 1625 to 1634: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1625 : List ℚ := [33825/256]
def b1626 : List ℚ := [8475/64]
def b1627 : List ℚ := [33975/256]
def b1628 : List ℚ := [17025/128]
def b1629 : List ℚ := [34125/256]
def b1630 : List ℚ := [4275/32]
def b1631 : List ℚ := [34275/256]
def b1632 : List ℚ := [17175/128]
def b1633 : List ℚ := [34425/256]
def b1634 : List ℚ := [8625/64]

def breaks1625 : List (List ℚ) := [b1625, b1626, b1627, b1628, b1629, b1630, b1631, b1632, b1633, b1634]

theorem c1625 : checkCell pa19 (cellAt 1625) b1625 = true := by decide +kernel

theorem c1626 : checkCell pa19 (cellAt 1626) b1626 = true := by decide +kernel

theorem c1627 : checkCell pa19 (cellAt 1627) b1627 = true := by decide +kernel

theorem c1628 : checkCell pa19 (cellAt 1628) b1628 = true := by decide +kernel

theorem c1629 : checkCell pa19 (cellAt 1629) b1629 = true := by decide +kernel

theorem c1630 : checkCell pa19 (cellAt 1630) b1630 = true := by decide +kernel

theorem c1631 : checkCell pa19 (cellAt 1631) b1631 = true := by decide +kernel

theorem c1632 : checkCell pa19 (cellAt 1632) b1632 = true := by decide +kernel

theorem c1633 : checkCell pa19 (cellAt 1633) b1633 = true := by decide +kernel

theorem c1634 : checkCell pa19 (cellAt 1634) b1634 = true := by decide +kernel

theorem slice1625 : slice 1625 10 = [cellAt 1625, cellAt 1626, cellAt 1627, cellAt 1628, cellAt 1629, cellAt 1630, cellAt 1631, cellAt 1632, cellAt 1633, cellAt 1634] := by decide +kernel

theorem batch1625_ok : checkAll pa19 (slice 1625 10) breaks1625 = true := by
  rw [slice1625]
  simp only [breaks1625, checkAll, c1625, c1626, c1627, c1628, c1629, c1630, c1631, c1632, c1633, c1634, Bool.and_self]

theorem batch1625 : ∀ c ∈ slice 1625 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1625_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1625
