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

/-! Serialized cells 845 to 854: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0845 : List ℚ := [5475/1024]
def b0846 : List ℚ := [11025/2048]
def b0847 : List ℚ := [2775/512]
def b0848 : List ℚ := [11175/2048]
def b0849 : List ℚ := [5625/1024]
def b0850 : List ℚ := [11325/2048]
def b0851 : List ℚ := [1425/256]
def b0852 : List ℚ := [11475/2048]
def b0853 : List ℚ := [5775/1024]
def b0854 : List ℚ := [11625/2048]

def breaks0845 : List (List ℚ) := [b0845, b0846, b0847, b0848, b0849, b0850, b0851, b0852, b0853, b0854]

theorem c0845 : checkCell pa19 (cellAt 845) b0845 = true := by decide +kernel

theorem c0846 : checkCell pa19 (cellAt 846) b0846 = true := by decide +kernel

theorem c0847 : checkCell pa19 (cellAt 847) b0847 = true := by decide +kernel

theorem c0848 : checkCell pa19 (cellAt 848) b0848 = true := by decide +kernel

theorem c0849 : checkCell pa19 (cellAt 849) b0849 = true := by decide +kernel

theorem c0850 : checkCell pa19 (cellAt 850) b0850 = true := by decide +kernel

theorem c0851 : checkCell pa19 (cellAt 851) b0851 = true := by decide +kernel

theorem c0852 : checkCell pa19 (cellAt 852) b0852 = true := by decide +kernel

theorem c0853 : checkCell pa19 (cellAt 853) b0853 = true := by decide +kernel

theorem c0854 : checkCell pa19 (cellAt 854) b0854 = true := by decide +kernel

theorem slice0845 : slice 845 10 = [cellAt 845, cellAt 846, cellAt 847, cellAt 848, cellAt 849, cellAt 850, cellAt 851, cellAt 852, cellAt 853, cellAt 854] := by decide +kernel

theorem batch0845_ok : checkAll pa19 (slice 845 10) breaks0845 = true := by
  rw [slice0845]
  simp only [breaks0845, checkAll, c0845, c0846, c0847, c0848, c0849, c0850, c0851, c0852, c0853, c0854, Bool.and_self]

theorem batch0845 : ∀ c ∈ slice 845 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0845_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0845
