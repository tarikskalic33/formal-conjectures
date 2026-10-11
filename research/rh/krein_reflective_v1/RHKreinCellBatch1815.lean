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

/-! Serialized cells 1815 to 1824: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1815 : List ℚ := [48075/256]
def b1816 : List ℚ := [24075/128]
def b1817 : List ℚ := [48225/256]
def b1818 : List ℚ := [12075/64]
def b1819 : List ℚ := [48375/256]
def b1820 : List ℚ := [96825/512, 24225/128]
def b1821 : List ℚ := [96975/512, 48525/256]
def b1822 : List ℚ := [97125/512, 6075/32]
def b1823 : List ℚ := [97275/512, 48675/256]
def b1824 : List ℚ := [97425/512, 24375/128]

def breaks1815 : List (List ℚ) := [b1815, b1816, b1817, b1818, b1819, b1820, b1821, b1822, b1823, b1824]

theorem c1815 : checkCell pa19 (cellAt 1815) b1815 = true := by decide +kernel

theorem c1816 : checkCell pa19 (cellAt 1816) b1816 = true := by decide +kernel

theorem c1817 : checkCell pa19 (cellAt 1817) b1817 = true := by decide +kernel

theorem c1818 : checkCell pa19 (cellAt 1818) b1818 = true := by decide +kernel

theorem c1819 : checkCell pa19 (cellAt 1819) b1819 = true := by decide +kernel

theorem c1820 : checkCell pa19 (cellAt 1820) b1820 = true := by decide +kernel

theorem c1821 : checkCell pa19 (cellAt 1821) b1821 = true := by decide +kernel

theorem c1822 : checkCell pa19 (cellAt 1822) b1822 = true := by decide +kernel

theorem c1823 : checkCell pa19 (cellAt 1823) b1823 = true := by decide +kernel

theorem c1824 : checkCell pa19 (cellAt 1824) b1824 = true := by decide +kernel

theorem slice1815 : slice 1815 10 = [cellAt 1815, cellAt 1816, cellAt 1817, cellAt 1818, cellAt 1819, cellAt 1820, cellAt 1821, cellAt 1822, cellAt 1823, cellAt 1824] := by decide +kernel

theorem batch1815_ok : checkAll pa19 (slice 1815 10) breaks1815 = true := by
  rw [slice1815]
  simp only [breaks1815, checkAll, c1815, c1816, c1817, c1818, c1819, c1820, c1821, c1822, c1823, c1824, Bool.and_self]

theorem batch1815 : ∀ c ∈ slice 1815 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1815_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1815
