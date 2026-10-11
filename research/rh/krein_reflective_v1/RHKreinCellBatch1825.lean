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

/-! Serialized cells 1825 to 1834: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1825 : List ℚ := [97575/512, 48825/256]
def b1826 : List ℚ := [97725/512, 12225/64]
def b1827 : List ℚ := [97875/512, 48975/256]
def b1828 : List ℚ := [98025/512, 24525/128]
def b1829 : List ℚ := [98175/512, 49125/256]
def b1830 : List ℚ := [98325/512, 3075/16]
def b1831 : List ℚ := [98475/512, 49275/256]
def b1832 : List ℚ := [24675/128]
def b1833 : List ℚ := [49425/256]
def b1834 : List ℚ := [12375/64]

def breaks1825 : List (List ℚ) := [b1825, b1826, b1827, b1828, b1829, b1830, b1831, b1832, b1833, b1834]

theorem c1825 : checkCell pa19 (cellAt 1825) b1825 = true := by decide +kernel

theorem c1826 : checkCell pa19 (cellAt 1826) b1826 = true := by decide +kernel

theorem c1827 : checkCell pa19 (cellAt 1827) b1827 = true := by decide +kernel

theorem c1828 : checkCell pa19 (cellAt 1828) b1828 = true := by decide +kernel

theorem c1829 : checkCell pa19 (cellAt 1829) b1829 = true := by decide +kernel

theorem c1830 : checkCell pa19 (cellAt 1830) b1830 = true := by decide +kernel

theorem c1831 : checkCell pa19 (cellAt 1831) b1831 = true := by decide +kernel

theorem c1832 : checkCell pa19 (cellAt 1832) b1832 = true := by decide +kernel

theorem c1833 : checkCell pa19 (cellAt 1833) b1833 = true := by decide +kernel

theorem c1834 : checkCell pa19 (cellAt 1834) b1834 = true := by decide +kernel

theorem slice1825 : slice 1825 10 = [cellAt 1825, cellAt 1826, cellAt 1827, cellAt 1828, cellAt 1829, cellAt 1830, cellAt 1831, cellAt 1832, cellAt 1833, cellAt 1834] := by decide +kernel

theorem batch1825_ok : checkAll pa19 (slice 1825 10) breaks1825 = true := by
  rw [slice1825]
  simp only [breaks1825, checkAll, c1825, c1826, c1827, c1828, c1829, c1830, c1831, c1832, c1833, c1834, Bool.and_self]

theorem batch1825 : ∀ c ∈ slice 1825 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1825_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1825
