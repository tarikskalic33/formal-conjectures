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

/-! Serialized cells 1855 to 1864: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1855 : List ℚ := [51075/256]
def b1856 : List ℚ := [102225/512, 25575/128]
def b1857 : List ℚ := [102375/512, 51225/256]
def b1858 : List ℚ := [102525/512, 12825/64]
def b1859 : List ℚ := [51375/256]
def b1860 : List ℚ := [25725/128]
def b1861 : List ℚ := [51525/256]
def b1862 : List ℚ := [3225/16]
def b1863 : List ℚ := [51675/256]
def b1864 : List ℚ := [25875/128]

def breaks1855 : List (List ℚ) := [b1855, b1856, b1857, b1858, b1859, b1860, b1861, b1862, b1863, b1864]

theorem c1855 : checkCell pa19 (cellAt 1855) b1855 = true := by decide +kernel

theorem c1856 : checkCell pa19 (cellAt 1856) b1856 = true := by decide +kernel

theorem c1857 : checkCell pa19 (cellAt 1857) b1857 = true := by decide +kernel

theorem c1858 : checkCell pa19 (cellAt 1858) b1858 = true := by decide +kernel

theorem c1859 : checkCell pa19 (cellAt 1859) b1859 = true := by decide +kernel

theorem c1860 : checkCell pa19 (cellAt 1860) b1860 = true := by decide +kernel

theorem c1861 : checkCell pa19 (cellAt 1861) b1861 = true := by decide +kernel

theorem c1862 : checkCell pa19 (cellAt 1862) b1862 = true := by decide +kernel

theorem c1863 : checkCell pa19 (cellAt 1863) b1863 = true := by decide +kernel

theorem c1864 : checkCell pa19 (cellAt 1864) b1864 = true := by decide +kernel

theorem slice1855 : slice 1855 10 = [cellAt 1855, cellAt 1856, cellAt 1857, cellAt 1858, cellAt 1859, cellAt 1860, cellAt 1861, cellAt 1862, cellAt 1863, cellAt 1864] := by decide +kernel

theorem batch1855_ok : checkAll pa19 (slice 1855 10) breaks1855 = true := by
  rw [slice1855]
  simp only [breaks1855, checkAll, c1855, c1856, c1857, c1858, c1859, c1860, c1861, c1862, c1863, c1864, Bool.and_self]

theorem batch1855 : ∀ c ∈ slice 1855 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1855_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1855
