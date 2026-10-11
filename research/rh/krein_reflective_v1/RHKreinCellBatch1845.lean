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

/-! Serialized cells 1845 to 1854: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1845 : List ℚ := [50325/256]
def b1846 : List ℚ := [1575/8]
def b1847 : List ℚ := [50475/256]
def b1848 : List ℚ := [25275/128]
def b1849 : List ℚ := [50625/256]
def b1850 : List ℚ := [12675/64]
def b1851 : List ℚ := [50775/256]
def b1852 : List ℚ := [25425/128]
def b1853 : List ℚ := [50925/256]
def b1854 : List ℚ := [6375/32]

def breaks1845 : List (List ℚ) := [b1845, b1846, b1847, b1848, b1849, b1850, b1851, b1852, b1853, b1854]

theorem c1845 : checkCell pa19 (cellAt 1845) b1845 = true := by decide +kernel

theorem c1846 : checkCell pa19 (cellAt 1846) b1846 = true := by decide +kernel

theorem c1847 : checkCell pa19 (cellAt 1847) b1847 = true := by decide +kernel

theorem c1848 : checkCell pa19 (cellAt 1848) b1848 = true := by decide +kernel

theorem c1849 : checkCell pa19 (cellAt 1849) b1849 = true := by decide +kernel

theorem c1850 : checkCell pa19 (cellAt 1850) b1850 = true := by decide +kernel

theorem c1851 : checkCell pa19 (cellAt 1851) b1851 = true := by decide +kernel

theorem c1852 : checkCell pa19 (cellAt 1852) b1852 = true := by decide +kernel

theorem c1853 : checkCell pa19 (cellAt 1853) b1853 = true := by decide +kernel

theorem c1854 : checkCell pa19 (cellAt 1854) b1854 = true := by decide +kernel

theorem slice1845 : slice 1845 10 = [cellAt 1845, cellAt 1846, cellAt 1847, cellAt 1848, cellAt 1849, cellAt 1850, cellAt 1851, cellAt 1852, cellAt 1853, cellAt 1854] := by decide +kernel

theorem batch1845_ok : checkAll pa19 (slice 1845 10) breaks1845 = true := by
  rw [slice1845]
  simp only [breaks1845, checkAll, c1845, c1846, c1847, c1848, c1849, c1850, c1851, c1852, c1853, c1854, Bool.and_self]

theorem batch1845 : ∀ c ∈ slice 1845 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1845_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1845
