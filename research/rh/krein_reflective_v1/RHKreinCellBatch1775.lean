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

/-! Serialized cells 1775 to 1784: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1775 : List ℚ := [45075/256]
def b1776 : List ℚ := [22575/128]
def b1777 : List ℚ := [45225/256]
def b1778 : List ℚ := [11325/64]
def b1779 : List ℚ := [45375/256]
def b1780 : List ℚ := [22725/128]
def b1781 : List ℚ := [45525/256]
def b1782 : List ℚ := [1425/8]
def b1783 : List ℚ := [45675/256]
def b1784 : List ℚ := [22875/128]

def breaks1775 : List (List ℚ) := [b1775, b1776, b1777, b1778, b1779, b1780, b1781, b1782, b1783, b1784]

theorem c1775 : checkCell pa19 (cellAt 1775) b1775 = true := by decide +kernel

theorem c1776 : checkCell pa19 (cellAt 1776) b1776 = true := by decide +kernel

theorem c1777 : checkCell pa19 (cellAt 1777) b1777 = true := by decide +kernel

theorem c1778 : checkCell pa19 (cellAt 1778) b1778 = true := by decide +kernel

theorem c1779 : checkCell pa19 (cellAt 1779) b1779 = true := by decide +kernel

theorem c1780 : checkCell pa19 (cellAt 1780) b1780 = true := by decide +kernel

theorem c1781 : checkCell pa19 (cellAt 1781) b1781 = true := by decide +kernel

theorem c1782 : checkCell pa19 (cellAt 1782) b1782 = true := by decide +kernel

theorem c1783 : checkCell pa19 (cellAt 1783) b1783 = true := by decide +kernel

theorem c1784 : checkCell pa19 (cellAt 1784) b1784 = true := by decide +kernel

theorem slice1775 : slice 1775 10 = [cellAt 1775, cellAt 1776, cellAt 1777, cellAt 1778, cellAt 1779, cellAt 1780, cellAt 1781, cellAt 1782, cellAt 1783, cellAt 1784] := by decide +kernel

theorem batch1775_ok : checkAll pa19 (slice 1775 10) breaks1775 = true := by
  rw [slice1775]
  simp only [breaks1775, checkAll, c1775, c1776, c1777, c1778, c1779, c1780, c1781, c1782, c1783, c1784, Bool.and_self]

theorem batch1775 : ∀ c ∈ slice 1775 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1775_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1775
