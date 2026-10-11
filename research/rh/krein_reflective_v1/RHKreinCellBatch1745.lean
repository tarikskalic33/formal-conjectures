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

/-! Serialized cells 1745 to 1754: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1745 : List ℚ := [42825/256]
def b1746 : List ℚ := [10725/64]
def b1747 : List ℚ := [42975/256]
def b1748 : List ℚ := [21525/128]
def b1749 : List ℚ := [43125/256]
def b1750 : List ℚ := [675/4]
def b1751 : List ℚ := [43275/256]
def b1752 : List ℚ := [21675/128]
def b1753 : List ℚ := [43425/256]
def b1754 : List ℚ := [10875/64]

def breaks1745 : List (List ℚ) := [b1745, b1746, b1747, b1748, b1749, b1750, b1751, b1752, b1753, b1754]

theorem c1745 : checkCell pa19 (cellAt 1745) b1745 = true := by decide +kernel

theorem c1746 : checkCell pa19 (cellAt 1746) b1746 = true := by decide +kernel

theorem c1747 : checkCell pa19 (cellAt 1747) b1747 = true := by decide +kernel

theorem c1748 : checkCell pa19 (cellAt 1748) b1748 = true := by decide +kernel

theorem c1749 : checkCell pa19 (cellAt 1749) b1749 = true := by decide +kernel

theorem c1750 : checkCell pa19 (cellAt 1750) b1750 = true := by decide +kernel

theorem c1751 : checkCell pa19 (cellAt 1751) b1751 = true := by decide +kernel

theorem c1752 : checkCell pa19 (cellAt 1752) b1752 = true := by decide +kernel

theorem c1753 : checkCell pa19 (cellAt 1753) b1753 = true := by decide +kernel

theorem c1754 : checkCell pa19 (cellAt 1754) b1754 = true := by decide +kernel

theorem slice1745 : slice 1745 10 = [cellAt 1745, cellAt 1746, cellAt 1747, cellAt 1748, cellAt 1749, cellAt 1750, cellAt 1751, cellAt 1752, cellAt 1753, cellAt 1754] := by decide +kernel

theorem batch1745_ok : checkAll pa19 (slice 1745 10) breaks1745 = true := by
  rw [slice1745]
  simp only [breaks1745, checkAll, c1745, c1746, c1747, c1748, c1749, c1750, c1751, c1752, c1753, c1754, Bool.and_self]

theorem batch1745 : ∀ c ∈ slice 1745 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1745_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1745
