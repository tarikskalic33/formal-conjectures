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

/-! Serialized cells 785 to 794: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0785 : List ℚ := [3825/1024]
def b0786 : List ℚ := [15375/4096]
def b0787 : List ℚ := [7725/2048]
def b0788 : List ℚ := [15525/4096]
def b0789 : List ℚ := [975/256]
def b0790 : List ℚ := [15675/4096]
def b0791 : List ℚ := [7875/2048]
def b0792 : List ℚ := [15825/4096]
def b0793 : List ℚ := [3975/1024]
def b0794 : List ℚ := [15975/4096]

def breaks0785 : List (List ℚ) := [b0785, b0786, b0787, b0788, b0789, b0790, b0791, b0792, b0793, b0794]

theorem c0785 : checkCell pa19 (cellAt 785) b0785 = true := by decide +kernel

theorem c0786 : checkCell pa19 (cellAt 786) b0786 = true := by decide +kernel

theorem c0787 : checkCell pa19 (cellAt 787) b0787 = true := by decide +kernel

theorem c0788 : checkCell pa19 (cellAt 788) b0788 = true := by decide +kernel

theorem c0789 : checkCell pa19 (cellAt 789) b0789 = true := by decide +kernel

theorem c0790 : checkCell pa19 (cellAt 790) b0790 = true := by decide +kernel

theorem c0791 : checkCell pa19 (cellAt 791) b0791 = true := by decide +kernel

theorem c0792 : checkCell pa19 (cellAt 792) b0792 = true := by decide +kernel

theorem c0793 : checkCell pa19 (cellAt 793) b0793 = true := by decide +kernel

theorem c0794 : checkCell pa19 (cellAt 794) b0794 = true := by decide +kernel

theorem slice0785 : slice 785 10 = [cellAt 785, cellAt 786, cellAt 787, cellAt 788, cellAt 789, cellAt 790, cellAt 791, cellAt 792, cellAt 793, cellAt 794] := by decide +kernel

theorem batch0785_ok : checkAll pa19 (slice 785 10) breaks0785 = true := by
  rw [slice0785]
  simp only [breaks0785, checkAll, c0785, c0786, c0787, c0788, c0789, c0790, c0791, c0792, c0793, c0794, Bool.and_self]

theorem batch0785 : ∀ c ∈ slice 785 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0785_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0785
