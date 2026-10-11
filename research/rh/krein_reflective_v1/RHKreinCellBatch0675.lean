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

/-! Serialized cells 675 to 684: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0675 : List ℚ := [16425/8192]
def b0676 : List ℚ := [4125/2048]
def b0677 : List ℚ := [16575/8192]
def b0678 : List ℚ := [8325/4096]
def b0679 : List ℚ := [16725/8192]
def b0680 : List ℚ := [525/256]
def b0681 : List ℚ := [16875/8192]
def b0682 : List ℚ := [8475/4096]
def b0683 : List ℚ := [17025/8192]
def b0684 : List ℚ := [4275/2048]

def breaks0675 : List (List ℚ) := [b0675, b0676, b0677, b0678, b0679, b0680, b0681, b0682, b0683, b0684]

theorem c0675 : checkCell pa19 (cellAt 675) b0675 = true := by decide +kernel

theorem c0676 : checkCell pa19 (cellAt 676) b0676 = true := by decide +kernel

theorem c0677 : checkCell pa19 (cellAt 677) b0677 = true := by decide +kernel

theorem c0678 : checkCell pa19 (cellAt 678) b0678 = true := by decide +kernel

theorem c0679 : checkCell pa19 (cellAt 679) b0679 = true := by decide +kernel

theorem c0680 : checkCell pa19 (cellAt 680) b0680 = true := by decide +kernel

theorem c0681 : checkCell pa19 (cellAt 681) b0681 = true := by decide +kernel

theorem c0682 : checkCell pa19 (cellAt 682) b0682 = true := by decide +kernel

theorem c0683 : checkCell pa19 (cellAt 683) b0683 = true := by decide +kernel

theorem c0684 : checkCell pa19 (cellAt 684) b0684 = true := by decide +kernel

theorem slice0675 : slice 675 10 = [cellAt 675, cellAt 676, cellAt 677, cellAt 678, cellAt 679, cellAt 680, cellAt 681, cellAt 682, cellAt 683, cellAt 684] := by decide +kernel

theorem batch0675_ok : checkAll pa19 (slice 675 10) breaks0675 = true := by
  rw [slice0675]
  simp only [breaks0675, checkAll, c0675, c0676, c0677, c0678, c0679, c0680, c0681, c0682, c0683, c0684, Bool.and_self]

theorem batch0675 : ∀ c ∈ slice 675 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0675_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0675
