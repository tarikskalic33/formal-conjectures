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

/-! Serialized cells 1155 to 1164: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1155 : List ℚ := [39075/2048]
def b1156 : List ℚ := [19575/1024]
def b1157 : List ℚ := [39225/2048]
def b1158 : List ℚ := [9825/512]
def b1159 : List ℚ := [39375/2048]
def b1160 : List ℚ := [19725/1024]
def b1161 : List ℚ := [39525/2048]
def b1162 : List ℚ := [2475/128]
def b1163 : List ℚ := [39675/2048]
def b1164 : List ℚ := [19875/1024]

def breaks1155 : List (List ℚ) := [b1155, b1156, b1157, b1158, b1159, b1160, b1161, b1162, b1163, b1164]

theorem c1155 : checkCell pa19 (cellAt 1155) b1155 = true := by decide +kernel

theorem c1156 : checkCell pa19 (cellAt 1156) b1156 = true := by decide +kernel

theorem c1157 : checkCell pa19 (cellAt 1157) b1157 = true := by decide +kernel

theorem c1158 : checkCell pa19 (cellAt 1158) b1158 = true := by decide +kernel

theorem c1159 : checkCell pa19 (cellAt 1159) b1159 = true := by decide +kernel

theorem c1160 : checkCell pa19 (cellAt 1160) b1160 = true := by decide +kernel

theorem c1161 : checkCell pa19 (cellAt 1161) b1161 = true := by decide +kernel

theorem c1162 : checkCell pa19 (cellAt 1162) b1162 = true := by decide +kernel

theorem c1163 : checkCell pa19 (cellAt 1163) b1163 = true := by decide +kernel

theorem c1164 : checkCell pa19 (cellAt 1164) b1164 = true := by decide +kernel

theorem slice1155 : slice 1155 10 = [cellAt 1155, cellAt 1156, cellAt 1157, cellAt 1158, cellAt 1159, cellAt 1160, cellAt 1161, cellAt 1162, cellAt 1163, cellAt 1164] := by decide +kernel

theorem batch1155_ok : checkAll pa19 (slice 1155 10) breaks1155 = true := by
  rw [slice1155]
  simp only [breaks1155, checkAll, c1155, c1156, c1157, c1158, c1159, c1160, c1161, c1162, c1163, c1164, Bool.and_self]

theorem batch1155 : ∀ c ∈ slice 1155 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1155_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1155
