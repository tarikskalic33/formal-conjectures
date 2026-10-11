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

/-! Serialized cells 1875 to 1884: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1875 : List ℚ := [52575/256]
def b1876 : List ℚ := [26325/128]
def b1877 : List ℚ := [52725/256]
def b1878 : List ℚ := [825/4]
def b1879 : List ℚ := [52875/256]
def b1880 : List ℚ := [26475/128]
def b1881 : List ℚ := [53025/256]
def b1882 : List ℚ := [13275/64]
def b1883 : List ℚ := [53175/256]
def b1884 : List ℚ := [26625/128]

def breaks1875 : List (List ℚ) := [b1875, b1876, b1877, b1878, b1879, b1880, b1881, b1882, b1883, b1884]

theorem c1875 : checkCell pa19 (cellAt 1875) b1875 = true := by decide +kernel

theorem c1876 : checkCell pa19 (cellAt 1876) b1876 = true := by decide +kernel

theorem c1877 : checkCell pa19 (cellAt 1877) b1877 = true := by decide +kernel

theorem c1878 : checkCell pa19 (cellAt 1878) b1878 = true := by decide +kernel

theorem c1879 : checkCell pa19 (cellAt 1879) b1879 = true := by decide +kernel

theorem c1880 : checkCell pa19 (cellAt 1880) b1880 = true := by decide +kernel

theorem c1881 : checkCell pa19 (cellAt 1881) b1881 = true := by decide +kernel

theorem c1882 : checkCell pa19 (cellAt 1882) b1882 = true := by decide +kernel

theorem c1883 : checkCell pa19 (cellAt 1883) b1883 = true := by decide +kernel

theorem c1884 : checkCell pa19 (cellAt 1884) b1884 = true := by decide +kernel

theorem slice1875 : slice 1875 10 = [cellAt 1875, cellAt 1876, cellAt 1877, cellAt 1878, cellAt 1879, cellAt 1880, cellAt 1881, cellAt 1882, cellAt 1883, cellAt 1884] := by decide +kernel

theorem batch1875_ok : checkAll pa19 (slice 1875 10) breaks1875 = true := by
  rw [slice1875]
  simp only [breaks1875, checkAll, c1875, c1876, c1877, c1878, c1879, c1880, c1881, c1882, c1883, c1884, Bool.and_self]

theorem batch1875 : ∀ c ∈ slice 1875 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1875_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1875
