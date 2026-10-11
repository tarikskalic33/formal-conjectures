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

/-! Serialized cells 1795 to 1804: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1795 : List ℚ := [46575/256]
def b1796 : List ℚ := [23325/128]
def b1797 : List ℚ := [46725/256]
def b1798 : List ℚ := [93525/512, 2925/16]
def b1799 : List ℚ := [93675/512, 46875/256]
def b1800 : List ℚ := [93825/512, 23475/128]
def b1801 : List ℚ := [47025/256]
def b1802 : List ℚ := [11775/64]
def b1803 : List ℚ := [47175/256]
def b1804 : List ℚ := [23625/128]

def breaks1795 : List (List ℚ) := [b1795, b1796, b1797, b1798, b1799, b1800, b1801, b1802, b1803, b1804]

theorem c1795 : checkCell pa19 (cellAt 1795) b1795 = true := by decide +kernel

theorem c1796 : checkCell pa19 (cellAt 1796) b1796 = true := by decide +kernel

theorem c1797 : checkCell pa19 (cellAt 1797) b1797 = true := by decide +kernel

theorem c1798 : checkCell pa19 (cellAt 1798) b1798 = true := by decide +kernel

theorem c1799 : checkCell pa19 (cellAt 1799) b1799 = true := by decide +kernel

theorem c1800 : checkCell pa19 (cellAt 1800) b1800 = true := by decide +kernel

theorem c1801 : checkCell pa19 (cellAt 1801) b1801 = true := by decide +kernel

theorem c1802 : checkCell pa19 (cellAt 1802) b1802 = true := by decide +kernel

theorem c1803 : checkCell pa19 (cellAt 1803) b1803 = true := by decide +kernel

theorem c1804 : checkCell pa19 (cellAt 1804) b1804 = true := by decide +kernel

theorem slice1795 : slice 1795 10 = [cellAt 1795, cellAt 1796, cellAt 1797, cellAt 1798, cellAt 1799, cellAt 1800, cellAt 1801, cellAt 1802, cellAt 1803, cellAt 1804] := by decide +kernel

theorem batch1795_ok : checkAll pa19 (slice 1795 10) breaks1795 = true := by
  rw [slice1795]
  simp only [breaks1795, checkAll, c1795, c1796, c1797, c1798, c1799, c1800, c1801, c1802, c1803, c1804, Bool.and_self]

theorem batch1795 : ∀ c ∈ slice 1795 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1795_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1795
