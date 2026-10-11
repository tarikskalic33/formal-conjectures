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

/-! Serialized cells 1735 to 1744: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1735 : List ℚ := [42075/256]
def b1736 : List ℚ := [21075/128]
def b1737 : List ℚ := [42225/256]
def b1738 : List ℚ := [10575/64]
def b1739 : List ℚ := [42375/256]
def b1740 : List ℚ := [21225/128]
def b1741 : List ℚ := [42525/256]
def b1742 : List ℚ := [5325/32]
def b1743 : List ℚ := [42675/256]
def b1744 : List ℚ := [21375/128]

def breaks1735 : List (List ℚ) := [b1735, b1736, b1737, b1738, b1739, b1740, b1741, b1742, b1743, b1744]

theorem c1735 : checkCell pa19 (cellAt 1735) b1735 = true := by decide +kernel

theorem c1736 : checkCell pa19 (cellAt 1736) b1736 = true := by decide +kernel

theorem c1737 : checkCell pa19 (cellAt 1737) b1737 = true := by decide +kernel

theorem c1738 : checkCell pa19 (cellAt 1738) b1738 = true := by decide +kernel

theorem c1739 : checkCell pa19 (cellAt 1739) b1739 = true := by decide +kernel

theorem c1740 : checkCell pa19 (cellAt 1740) b1740 = true := by decide +kernel

theorem c1741 : checkCell pa19 (cellAt 1741) b1741 = true := by decide +kernel

theorem c1742 : checkCell pa19 (cellAt 1742) b1742 = true := by decide +kernel

theorem c1743 : checkCell pa19 (cellAt 1743) b1743 = true := by decide +kernel

theorem c1744 : checkCell pa19 (cellAt 1744) b1744 = true := by decide +kernel

theorem slice1735 : slice 1735 10 = [cellAt 1735, cellAt 1736, cellAt 1737, cellAt 1738, cellAt 1739, cellAt 1740, cellAt 1741, cellAt 1742, cellAt 1743, cellAt 1744] := by decide +kernel

theorem batch1735_ok : checkAll pa19 (slice 1735 10) breaks1735 = true := by
  rw [slice1735]
  simp only [breaks1735, checkAll, c1735, c1736, c1737, c1738, c1739, c1740, c1741, c1742, c1743, c1744, Bool.and_self]

theorem batch1735 : ∀ c ∈ slice 1735 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1735_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1735
