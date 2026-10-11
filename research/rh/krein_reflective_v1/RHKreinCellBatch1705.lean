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

/-! Serialized cells 1705 to 1714: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1705 : List ℚ := [39825/256]
def b1706 : List ℚ := [9975/64]
def b1707 : List ℚ := [39975/256]
def b1708 : List ℚ := [20025/128]
def b1709 : List ℚ := [40125/256]
def b1710 : List ℚ := [5025/32]
def b1711 : List ℚ := [40275/256]
def b1712 : List ℚ := [20175/128]
def b1713 : List ℚ := [40425/256]
def b1714 : List ℚ := [10125/64]

def breaks1705 : List (List ℚ) := [b1705, b1706, b1707, b1708, b1709, b1710, b1711, b1712, b1713, b1714]

theorem c1705 : checkCell pa19 (cellAt 1705) b1705 = true := by decide +kernel

theorem c1706 : checkCell pa19 (cellAt 1706) b1706 = true := by decide +kernel

theorem c1707 : checkCell pa19 (cellAt 1707) b1707 = true := by decide +kernel

theorem c1708 : checkCell pa19 (cellAt 1708) b1708 = true := by decide +kernel

theorem c1709 : checkCell pa19 (cellAt 1709) b1709 = true := by decide +kernel

theorem c1710 : checkCell pa19 (cellAt 1710) b1710 = true := by decide +kernel

theorem c1711 : checkCell pa19 (cellAt 1711) b1711 = true := by decide +kernel

theorem c1712 : checkCell pa19 (cellAt 1712) b1712 = true := by decide +kernel

theorem c1713 : checkCell pa19 (cellAt 1713) b1713 = true := by decide +kernel

theorem c1714 : checkCell pa19 (cellAt 1714) b1714 = true := by decide +kernel

theorem slice1705 : slice 1705 10 = [cellAt 1705, cellAt 1706, cellAt 1707, cellAt 1708, cellAt 1709, cellAt 1710, cellAt 1711, cellAt 1712, cellAt 1713, cellAt 1714] := by decide +kernel

theorem batch1705_ok : checkAll pa19 (slice 1705 10) breaks1705 = true := by
  rw [slice1705]
  simp only [breaks1705, checkAll, c1705, c1706, c1707, c1708, c1709, c1710, c1711, c1712, c1713, c1714, Bool.and_self]

theorem batch1705 : ∀ c ∈ slice 1705 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1705_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1705
