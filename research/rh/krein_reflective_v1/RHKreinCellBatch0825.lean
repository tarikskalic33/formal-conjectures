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

/-! Serialized cells 825 to 834: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0825 : List ℚ := [4725/1024]
def b0826 : List ℚ := [9525/2048]
def b0827 : List ℚ := [75/16]
def b0828 : List ℚ := [9675/2048]
def b0829 : List ℚ := [4875/1024]
def b0830 : List ℚ := [9825/2048]
def b0831 : List ℚ := [2475/512]
def b0832 : List ℚ := [9975/2048]
def b0833 : List ℚ := [5025/1024]
def b0834 : List ℚ := [10125/2048]

def breaks0825 : List (List ℚ) := [b0825, b0826, b0827, b0828, b0829, b0830, b0831, b0832, b0833, b0834]

theorem c0825 : checkCell pa19 (cellAt 825) b0825 = true := by decide +kernel

theorem c0826 : checkCell pa19 (cellAt 826) b0826 = true := by decide +kernel

theorem c0827 : checkCell pa19 (cellAt 827) b0827 = true := by decide +kernel

theorem c0828 : checkCell pa19 (cellAt 828) b0828 = true := by decide +kernel

theorem c0829 : checkCell pa19 (cellAt 829) b0829 = true := by decide +kernel

theorem c0830 : checkCell pa19 (cellAt 830) b0830 = true := by decide +kernel

theorem c0831 : checkCell pa19 (cellAt 831) b0831 = true := by decide +kernel

theorem c0832 : checkCell pa19 (cellAt 832) b0832 = true := by decide +kernel

theorem c0833 : checkCell pa19 (cellAt 833) b0833 = true := by decide +kernel

theorem c0834 : checkCell pa19 (cellAt 834) b0834 = true := by decide +kernel

theorem slice0825 : slice 825 10 = [cellAt 825, cellAt 826, cellAt 827, cellAt 828, cellAt 829, cellAt 830, cellAt 831, cellAt 832, cellAt 833, cellAt 834] := by decide +kernel

theorem batch0825_ok : checkAll pa19 (slice 825 10) breaks0825 = true := by
  rw [slice0825]
  simp only [breaks0825, checkAll, c0825, c0826, c0827, c0828, c0829, c0830, c0831, c0832, c0833, c0834, Bool.and_self]

theorem batch0825 : ∀ c ∈ slice 825 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0825_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0825
