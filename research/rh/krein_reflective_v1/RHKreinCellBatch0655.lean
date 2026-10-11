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

/-! Serialized cells 655 to 664: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0655 : List ℚ := [30075/16384]
def b0656 : List ℚ := [15075/8192]
def b0657 : List ℚ := [30225/16384]
def b0658 : List ℚ := [7575/4096]
def b0659 : List ℚ := [15225/8192]
def b0660 : List ℚ := [3825/2048]
def b0661 : List ℚ := [15375/8192]
def b0662 : List ℚ := [7725/4096]
def b0663 : List ℚ := [15525/8192]
def b0664 : List ℚ := [975/512]

def breaks0655 : List (List ℚ) := [b0655, b0656, b0657, b0658, b0659, b0660, b0661, b0662, b0663, b0664]

theorem c0655 : checkCell pa19 (cellAt 655) b0655 = true := by decide +kernel

theorem c0656 : checkCell pa19 (cellAt 656) b0656 = true := by decide +kernel

theorem c0657 : checkCell pa19 (cellAt 657) b0657 = true := by decide +kernel

theorem c0658 : checkCell pa19 (cellAt 658) b0658 = true := by decide +kernel

theorem c0659 : checkCell pa19 (cellAt 659) b0659 = true := by decide +kernel

theorem c0660 : checkCell pa19 (cellAt 660) b0660 = true := by decide +kernel

theorem c0661 : checkCell pa19 (cellAt 661) b0661 = true := by decide +kernel

theorem c0662 : checkCell pa19 (cellAt 662) b0662 = true := by decide +kernel

theorem c0663 : checkCell pa19 (cellAt 663) b0663 = true := by decide +kernel

theorem c0664 : checkCell pa19 (cellAt 664) b0664 = true := by decide +kernel

theorem slice0655 : slice 655 10 = [cellAt 655, cellAt 656, cellAt 657, cellAt 658, cellAt 659, cellAt 660, cellAt 661, cellAt 662, cellAt 663, cellAt 664] := by decide +kernel

theorem batch0655_ok : checkAll pa19 (slice 655 10) breaks0655 = true := by
  rw [slice0655]
  simp only [breaks0655, checkAll, c0655, c0656, c0657, c0658, c0659, c0660, c0661, c0662, c0663, c0664, Bool.and_self]

theorem batch0655 : ∀ c ∈ slice 655 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0655_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0655
