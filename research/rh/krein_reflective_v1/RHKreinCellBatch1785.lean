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

/-! Serialized cells 1785 to 1794: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1785 : List ℚ := [45825/256]
def b1786 : List ℚ := [11475/64]
def b1787 : List ℚ := [45975/256]
def b1788 : List ℚ := [23025/128]
def b1789 : List ℚ := [46125/256]
def b1790 : List ℚ := [92325/512, 5775/32]
def b1791 : List ℚ := [92475/512, 46275/256]
def b1792 : List ℚ := [92625/512, 23175/128]
def b1793 : List ℚ := [92775/512, 46425/256]
def b1794 : List ℚ := [11625/64]

def breaks1785 : List (List ℚ) := [b1785, b1786, b1787, b1788, b1789, b1790, b1791, b1792, b1793, b1794]

theorem c1785 : checkCell pa19 (cellAt 1785) b1785 = true := by decide +kernel

theorem c1786 : checkCell pa19 (cellAt 1786) b1786 = true := by decide +kernel

theorem c1787 : checkCell pa19 (cellAt 1787) b1787 = true := by decide +kernel

theorem c1788 : checkCell pa19 (cellAt 1788) b1788 = true := by decide +kernel

theorem c1789 : checkCell pa19 (cellAt 1789) b1789 = true := by decide +kernel

theorem c1790 : checkCell pa19 (cellAt 1790) b1790 = true := by decide +kernel

theorem c1791 : checkCell pa19 (cellAt 1791) b1791 = true := by decide +kernel

theorem c1792 : checkCell pa19 (cellAt 1792) b1792 = true := by decide +kernel

theorem c1793 : checkCell pa19 (cellAt 1793) b1793 = true := by decide +kernel

theorem c1794 : checkCell pa19 (cellAt 1794) b1794 = true := by decide +kernel

theorem slice1785 : slice 1785 10 = [cellAt 1785, cellAt 1786, cellAt 1787, cellAt 1788, cellAt 1789, cellAt 1790, cellAt 1791, cellAt 1792, cellAt 1793, cellAt 1794] := by decide +kernel

theorem batch1785_ok : checkAll pa19 (slice 1785 10) breaks1785 = true := by
  rw [slice1785]
  simp only [breaks1785, checkAll, c1785, c1786, c1787, c1788, c1789, c1790, c1791, c1792, c1793, c1794, Bool.and_self]

theorem batch1785 : ∀ c ∈ slice 1785 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1785_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1785
