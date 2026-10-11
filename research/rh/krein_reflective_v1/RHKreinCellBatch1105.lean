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

/-! Serialized cells 1105 to 1114: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1105 : List ℚ := [225/16]
def b1106 : List ℚ := [3675/256]
def b1107 : List ℚ := [1875/128]
def b1108 : List ℚ := [3825/256]
def b1109 : List ℚ := [975/64]
def b1110 : List ℚ := [3975/256]
def b1111 : List ℚ := [2025/128]
def b1112 : List ℚ := [8175/512]
def b1113 : List ℚ := [4125/256]
def b1114 : List ℚ := [16575/1024]

def breaks1105 : List (List ℚ) := [b1105, b1106, b1107, b1108, b1109, b1110, b1111, b1112, b1113, b1114]

theorem c1105 : checkCell pa19 (cellAt 1105) b1105 = true := by decide +kernel

theorem c1106 : checkCell pa19 (cellAt 1106) b1106 = true := by decide +kernel

theorem c1107 : checkCell pa19 (cellAt 1107) b1107 = true := by decide +kernel

theorem c1108 : checkCell pa19 (cellAt 1108) b1108 = true := by decide +kernel

theorem c1109 : checkCell pa19 (cellAt 1109) b1109 = true := by decide +kernel

theorem c1110 : checkCell pa19 (cellAt 1110) b1110 = true := by decide +kernel

theorem c1111 : checkCell pa19 (cellAt 1111) b1111 = true := by decide +kernel

theorem c1112 : checkCell pa19 (cellAt 1112) b1112 = true := by decide +kernel

theorem c1113 : checkCell pa19 (cellAt 1113) b1113 = true := by decide +kernel

theorem c1114 : checkCell pa19 (cellAt 1114) b1114 = true := by decide +kernel

theorem slice1105 : slice 1105 10 = [cellAt 1105, cellAt 1106, cellAt 1107, cellAt 1108, cellAt 1109, cellAt 1110, cellAt 1111, cellAt 1112, cellAt 1113, cellAt 1114] := by decide +kernel

theorem batch1105_ok : checkAll pa19 (slice 1105 10) breaks1105 = true := by
  rw [slice1105]
  simp only [breaks1105, checkAll, c1105, c1106, c1107, c1108, c1109, c1110, c1111, c1112, c1113, c1114, Bool.and_self]

theorem batch1105 : ∀ c ∈ slice 1105 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1105_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1105
