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

/-! Serialized cells 1755 to 1764: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1755 : List ℚ := [43575/256]
def b1756 : List ℚ := [21825/128]
def b1757 : List ℚ := [43725/256]
def b1758 : List ℚ := [5475/32]
def b1759 : List ℚ := [43875/256]
def b1760 : List ℚ := [21975/128]
def b1761 : List ℚ := [44025/256]
def b1762 : List ℚ := [88125/512, 11025/64]
def b1763 : List ℚ := [44175/256]
def b1764 : List ℚ := [22125/128]

def breaks1755 : List (List ℚ) := [b1755, b1756, b1757, b1758, b1759, b1760, b1761, b1762, b1763, b1764]

theorem c1755 : checkCell pa19 (cellAt 1755) b1755 = true := by decide +kernel

theorem c1756 : checkCell pa19 (cellAt 1756) b1756 = true := by decide +kernel

theorem c1757 : checkCell pa19 (cellAt 1757) b1757 = true := by decide +kernel

theorem c1758 : checkCell pa19 (cellAt 1758) b1758 = true := by decide +kernel

theorem c1759 : checkCell pa19 (cellAt 1759) b1759 = true := by decide +kernel

theorem c1760 : checkCell pa19 (cellAt 1760) b1760 = true := by decide +kernel

theorem c1761 : checkCell pa19 (cellAt 1761) b1761 = true := by decide +kernel

theorem c1762 : checkCell pa19 (cellAt 1762) b1762 = true := by decide +kernel

theorem c1763 : checkCell pa19 (cellAt 1763) b1763 = true := by decide +kernel

theorem c1764 : checkCell pa19 (cellAt 1764) b1764 = true := by decide +kernel

theorem slice1755 : slice 1755 10 = [cellAt 1755, cellAt 1756, cellAt 1757, cellAt 1758, cellAt 1759, cellAt 1760, cellAt 1761, cellAt 1762, cellAt 1763, cellAt 1764] := by decide +kernel

theorem batch1755_ok : checkAll pa19 (slice 1755 10) breaks1755 = true := by
  rw [slice1755]
  simp only [breaks1755, checkAll, c1755, c1756, c1757, c1758, c1759, c1760, c1761, c1762, c1763, c1764, Bool.and_self]

theorem batch1755 : ∀ c ∈ slice 1755 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1755_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1755
