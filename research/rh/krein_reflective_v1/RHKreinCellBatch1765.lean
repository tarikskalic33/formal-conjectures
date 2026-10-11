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

/-! Serialized cells 1765 to 1774: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1765 : List ℚ := [44325/256]
def b1766 : List ℚ := [2775/16]
def b1767 : List ℚ := [44475/256]
def b1768 : List ℚ := [22275/128]
def b1769 : List ℚ := [44625/256]
def b1770 : List ℚ := [11175/64]
def b1771 : List ℚ := [44775/256]
def b1772 : List ℚ := [22425/128]
def b1773 : List ℚ := [44925/256]
def b1774 : List ℚ := [5625/32]

def breaks1765 : List (List ℚ) := [b1765, b1766, b1767, b1768, b1769, b1770, b1771, b1772, b1773, b1774]

theorem c1765 : checkCell pa19 (cellAt 1765) b1765 = true := by decide +kernel

theorem c1766 : checkCell pa19 (cellAt 1766) b1766 = true := by decide +kernel

theorem c1767 : checkCell pa19 (cellAt 1767) b1767 = true := by decide +kernel

theorem c1768 : checkCell pa19 (cellAt 1768) b1768 = true := by decide +kernel

theorem c1769 : checkCell pa19 (cellAt 1769) b1769 = true := by decide +kernel

theorem c1770 : checkCell pa19 (cellAt 1770) b1770 = true := by decide +kernel

theorem c1771 : checkCell pa19 (cellAt 1771) b1771 = true := by decide +kernel

theorem c1772 : checkCell pa19 (cellAt 1772) b1772 = true := by decide +kernel

theorem c1773 : checkCell pa19 (cellAt 1773) b1773 = true := by decide +kernel

theorem c1774 : checkCell pa19 (cellAt 1774) b1774 = true := by decide +kernel

theorem slice1765 : slice 1765 10 = [cellAt 1765, cellAt 1766, cellAt 1767, cellAt 1768, cellAt 1769, cellAt 1770, cellAt 1771, cellAt 1772, cellAt 1773, cellAt 1774] := by decide +kernel

theorem batch1765_ok : checkAll pa19 (slice 1765 10) breaks1765 = true := by
  rw [slice1765]
  simp only [breaks1765, checkAll, c1765, c1766, c1767, c1768, c1769, c1770, c1771, c1772, c1773, c1774, Bool.and_self]

theorem batch1765 : ∀ c ∈ slice 1765 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1765_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1765
