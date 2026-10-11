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

/-! Serialized cells 1655 to 1664: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1655 : List ℚ := [36075/256]
def b1656 : List ℚ := [18075/128]
def b1657 : List ℚ := [36225/256]
def b1658 : List ℚ := [9075/64]
def b1659 : List ℚ := [36375/256]
def b1660 : List ℚ := [18225/128]
def b1661 : List ℚ := [36525/256]
def b1662 : List ℚ := [4575/32]
def b1663 : List ℚ := [36675/256]
def b1664 : List ℚ := [18375/128]

def breaks1655 : List (List ℚ) := [b1655, b1656, b1657, b1658, b1659, b1660, b1661, b1662, b1663, b1664]

theorem c1655 : checkCell pa19 (cellAt 1655) b1655 = true := by decide +kernel

theorem c1656 : checkCell pa19 (cellAt 1656) b1656 = true := by decide +kernel

theorem c1657 : checkCell pa19 (cellAt 1657) b1657 = true := by decide +kernel

theorem c1658 : checkCell pa19 (cellAt 1658) b1658 = true := by decide +kernel

theorem c1659 : checkCell pa19 (cellAt 1659) b1659 = true := by decide +kernel

theorem c1660 : checkCell pa19 (cellAt 1660) b1660 = true := by decide +kernel

theorem c1661 : checkCell pa19 (cellAt 1661) b1661 = true := by decide +kernel

theorem c1662 : checkCell pa19 (cellAt 1662) b1662 = true := by decide +kernel

theorem c1663 : checkCell pa19 (cellAt 1663) b1663 = true := by decide +kernel

theorem c1664 : checkCell pa19 (cellAt 1664) b1664 = true := by decide +kernel

theorem slice1655 : slice 1655 10 = [cellAt 1655, cellAt 1656, cellAt 1657, cellAt 1658, cellAt 1659, cellAt 1660, cellAt 1661, cellAt 1662, cellAt 1663, cellAt 1664] := by decide +kernel

theorem batch1655_ok : checkAll pa19 (slice 1655 10) breaks1655 = true := by
  rw [slice1655]
  simp only [breaks1655, checkAll, c1655, c1656, c1657, c1658, c1659, c1660, c1661, c1662, c1663, c1664, Bool.and_self]

theorem batch1655 : ∀ c ∈ slice 1655 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1655_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1655
