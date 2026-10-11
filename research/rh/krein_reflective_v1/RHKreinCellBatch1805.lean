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

/-! Serialized cells 1805 to 1814: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1805 : List ℚ := [47325/256]
def b1806 : List ℚ := [5925/32]
def b1807 : List ℚ := [47475/256]
def b1808 : List ℚ := [23775/128]
def b1809 : List ℚ := [47625/256]
def b1810 : List ℚ := [11925/64]
def b1811 : List ℚ := [47775/256]
def b1812 : List ℚ := [23925/128]
def b1813 : List ℚ := [47925/256]
def b1814 : List ℚ := [375/2]

def breaks1805 : List (List ℚ) := [b1805, b1806, b1807, b1808, b1809, b1810, b1811, b1812, b1813, b1814]

theorem c1805 : checkCell pa19 (cellAt 1805) b1805 = true := by decide +kernel

theorem c1806 : checkCell pa19 (cellAt 1806) b1806 = true := by decide +kernel

theorem c1807 : checkCell pa19 (cellAt 1807) b1807 = true := by decide +kernel

theorem c1808 : checkCell pa19 (cellAt 1808) b1808 = true := by decide +kernel

theorem c1809 : checkCell pa19 (cellAt 1809) b1809 = true := by decide +kernel

theorem c1810 : checkCell pa19 (cellAt 1810) b1810 = true := by decide +kernel

theorem c1811 : checkCell pa19 (cellAt 1811) b1811 = true := by decide +kernel

theorem c1812 : checkCell pa19 (cellAt 1812) b1812 = true := by decide +kernel

theorem c1813 : checkCell pa19 (cellAt 1813) b1813 = true := by decide +kernel

theorem c1814 : checkCell pa19 (cellAt 1814) b1814 = true := by decide +kernel

theorem slice1805 : slice 1805 10 = [cellAt 1805, cellAt 1806, cellAt 1807, cellAt 1808, cellAt 1809, cellAt 1810, cellAt 1811, cellAt 1812, cellAt 1813, cellAt 1814] := by decide +kernel

theorem batch1805_ok : checkAll pa19 (slice 1805 10) breaks1805 = true := by
  rw [slice1805]
  simp only [breaks1805, checkAll, c1805, c1806, c1807, c1808, c1809, c1810, c1811, c1812, c1813, c1814, Bool.and_self]

theorem batch1805 : ∀ c ∈ slice 1805 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1805_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1805
