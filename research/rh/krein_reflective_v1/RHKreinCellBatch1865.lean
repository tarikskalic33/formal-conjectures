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

/-! Serialized cells 1865 to 1874: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1865 : List ℚ := [51825/256]
def b1866 : List ℚ := [12975/64]
def b1867 : List ℚ := [51975/256]
def b1868 : List ℚ := [26025/128]
def b1869 : List ℚ := [52125/256]
def b1870 : List ℚ := [6525/32]
def b1871 : List ℚ := [52275/256]
def b1872 : List ℚ := [26175/128]
def b1873 : List ℚ := [52425/256]
def b1874 : List ℚ := [13125/64]

def breaks1865 : List (List ℚ) := [b1865, b1866, b1867, b1868, b1869, b1870, b1871, b1872, b1873, b1874]

theorem c1865 : checkCell pa19 (cellAt 1865) b1865 = true := by decide +kernel

theorem c1866 : checkCell pa19 (cellAt 1866) b1866 = true := by decide +kernel

theorem c1867 : checkCell pa19 (cellAt 1867) b1867 = true := by decide +kernel

theorem c1868 : checkCell pa19 (cellAt 1868) b1868 = true := by decide +kernel

theorem c1869 : checkCell pa19 (cellAt 1869) b1869 = true := by decide +kernel

theorem c1870 : checkCell pa19 (cellAt 1870) b1870 = true := by decide +kernel

theorem c1871 : checkCell pa19 (cellAt 1871) b1871 = true := by decide +kernel

theorem c1872 : checkCell pa19 (cellAt 1872) b1872 = true := by decide +kernel

theorem c1873 : checkCell pa19 (cellAt 1873) b1873 = true := by decide +kernel

theorem c1874 : checkCell pa19 (cellAt 1874) b1874 = true := by decide +kernel

theorem slice1865 : slice 1865 10 = [cellAt 1865, cellAt 1866, cellAt 1867, cellAt 1868, cellAt 1869, cellAt 1870, cellAt 1871, cellAt 1872, cellAt 1873, cellAt 1874] := by decide +kernel

theorem batch1865_ok : checkAll pa19 (slice 1865 10) breaks1865 = true := by
  rw [slice1865]
  simp only [breaks1865, checkAll, c1865, c1866, c1867, c1868, c1869, c1870, c1871, c1872, c1873, c1874, Bool.and_self]

theorem batch1865 : ∀ c ∈ slice 1865 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1865_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1865
