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

/-! Serialized cells 1095 to 1104: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1095 : List ℚ := [53325/4096]
def b1096 : List ℚ := [6675/512]
def b1097 : List ℚ := [26775/2048]
def b1098 : List ℚ := [13425/1024]
def b1099 : List ℚ := [26925/2048]
def b1100 : List ℚ := [3375/256]
def b1101 : List ℚ := [13575/1024]
def b1102 : List ℚ := [6825/512]
def b1103 : List ℚ := [1725/128]
def b1104 : List ℚ := [3525/256]

def breaks1095 : List (List ℚ) := [b1095, b1096, b1097, b1098, b1099, b1100, b1101, b1102, b1103, b1104]

theorem c1095 : checkCell pa19 (cellAt 1095) b1095 = true := by decide +kernel

theorem c1096 : checkCell pa19 (cellAt 1096) b1096 = true := by decide +kernel

theorem c1097 : checkCell pa19 (cellAt 1097) b1097 = true := by decide +kernel

theorem c1098 : checkCell pa19 (cellAt 1098) b1098 = true := by decide +kernel

theorem c1099 : checkCell pa19 (cellAt 1099) b1099 = true := by decide +kernel

theorem c1100 : checkCell pa19 (cellAt 1100) b1100 = true := by decide +kernel

theorem c1101 : checkCell pa19 (cellAt 1101) b1101 = true := by decide +kernel

theorem c1102 : checkCell pa19 (cellAt 1102) b1102 = true := by decide +kernel

theorem c1103 : checkCell pa19 (cellAt 1103) b1103 = true := by decide +kernel

theorem c1104 : checkCell pa19 (cellAt 1104) b1104 = true := by decide +kernel

theorem slice1095 : slice 1095 10 = [cellAt 1095, cellAt 1096, cellAt 1097, cellAt 1098, cellAt 1099, cellAt 1100, cellAt 1101, cellAt 1102, cellAt 1103, cellAt 1104] := by decide +kernel

theorem batch1095_ok : checkAll pa19 (slice 1095 10) breaks1095 = true := by
  rw [slice1095]
  simp only [breaks1095, checkAll, c1095, c1096, c1097, c1098, c1099, c1100, c1101, c1102, c1103, c1104, Bool.and_self]

theorem batch1095 : ∀ c ∈ slice 1095 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1095_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1095
