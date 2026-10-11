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

/-! Serialized cells 745 to 754: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0745 : List ℚ := [375/128]
def b0746 : List ℚ := [12075/4096]
def b0747 : List ℚ := [6075/2048]
def b0748 : List ℚ := [12225/4096]
def b0749 : List ℚ := [3075/1024]
def b0750 : List ℚ := [12375/4096]
def b0751 : List ℚ := [6225/2048]
def b0752 : List ℚ := [12525/4096]
def b0753 : List ℚ := [1575/512]
def b0754 : List ℚ := [12675/4096]

def breaks0745 : List (List ℚ) := [b0745, b0746, b0747, b0748, b0749, b0750, b0751, b0752, b0753, b0754]

theorem c0745 : checkCell pa19 (cellAt 745) b0745 = true := by decide +kernel

theorem c0746 : checkCell pa19 (cellAt 746) b0746 = true := by decide +kernel

theorem c0747 : checkCell pa19 (cellAt 747) b0747 = true := by decide +kernel

theorem c0748 : checkCell pa19 (cellAt 748) b0748 = true := by decide +kernel

theorem c0749 : checkCell pa19 (cellAt 749) b0749 = true := by decide +kernel

theorem c0750 : checkCell pa19 (cellAt 750) b0750 = true := by decide +kernel

theorem c0751 : checkCell pa19 (cellAt 751) b0751 = true := by decide +kernel

theorem c0752 : checkCell pa19 (cellAt 752) b0752 = true := by decide +kernel

theorem c0753 : checkCell pa19 (cellAt 753) b0753 = true := by decide +kernel

theorem c0754 : checkCell pa19 (cellAt 754) b0754 = true := by decide +kernel

theorem slice0745 : slice 745 10 = [cellAt 745, cellAt 746, cellAt 747, cellAt 748, cellAt 749, cellAt 750, cellAt 751, cellAt 752, cellAt 753, cellAt 754] := by decide +kernel

theorem batch0745_ok : checkAll pa19 (slice 745 10) breaks0745 = true := by
  rw [slice0745]
  simp only [breaks0745, checkAll, c0745, c0746, c0747, c0748, c0749, c0750, c0751, c0752, c0753, c0754, Bool.and_self]

theorem batch0745 : ∀ c ∈ slice 745 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0745_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0745
