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

/-! Serialized cells 1835 to 1844: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1835 : List ℚ := [49575/256]
def b1836 : List ℚ := [24825/128]
def b1837 : List ℚ := [49725/256]
def b1838 : List ℚ := [6225/32]
def b1839 : List ℚ := [49875/256]
def b1840 : List ℚ := [24975/128]
def b1841 : List ℚ := [50025/256]
def b1842 : List ℚ := [12525/64]
def b1843 : List ℚ := [50175/256]
def b1844 : List ℚ := [25125/128]

def breaks1835 : List (List ℚ) := [b1835, b1836, b1837, b1838, b1839, b1840, b1841, b1842, b1843, b1844]

theorem c1835 : checkCell pa19 (cellAt 1835) b1835 = true := by decide +kernel

theorem c1836 : checkCell pa19 (cellAt 1836) b1836 = true := by decide +kernel

theorem c1837 : checkCell pa19 (cellAt 1837) b1837 = true := by decide +kernel

theorem c1838 : checkCell pa19 (cellAt 1838) b1838 = true := by decide +kernel

theorem c1839 : checkCell pa19 (cellAt 1839) b1839 = true := by decide +kernel

theorem c1840 : checkCell pa19 (cellAt 1840) b1840 = true := by decide +kernel

theorem c1841 : checkCell pa19 (cellAt 1841) b1841 = true := by decide +kernel

theorem c1842 : checkCell pa19 (cellAt 1842) b1842 = true := by decide +kernel

theorem c1843 : checkCell pa19 (cellAt 1843) b1843 = true := by decide +kernel

theorem c1844 : checkCell pa19 (cellAt 1844) b1844 = true := by decide +kernel

theorem slice1835 : slice 1835 10 = [cellAt 1835, cellAt 1836, cellAt 1837, cellAt 1838, cellAt 1839, cellAt 1840, cellAt 1841, cellAt 1842, cellAt 1843, cellAt 1844] := by decide +kernel

theorem batch1835_ok : checkAll pa19 (slice 1835 10) breaks1835 = true := by
  rw [slice1835]
  simp only [breaks1835, checkAll, c1835, c1836, c1837, c1838, c1839, c1840, c1841, c1842, c1843, c1844, Bool.and_self]

theorem batch1835 : ∀ c ∈ slice 1835 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1835_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1835
