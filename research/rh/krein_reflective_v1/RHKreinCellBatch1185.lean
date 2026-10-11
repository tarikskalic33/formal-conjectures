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

/-! Serialized cells 1185 to 1194: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1185 : List ℚ := [40725/2048]
def b1186 : List ℚ := [81525/4096]
def b1187 : List ℚ := [1275/64]
def b1188 : List ℚ := [81675/4096]
def b1189 : List ℚ := [40875/2048]
def b1190 : List ℚ := [81825/4096]
def b1191 : List ℚ := [20475/1024]
def b1192 : List ℚ := [81975/4096]
def b1193 : List ℚ := [41025/2048]
def b1194 : List ℚ := [82125/4096]

def breaks1185 : List (List ℚ) := [b1185, b1186, b1187, b1188, b1189, b1190, b1191, b1192, b1193, b1194]

theorem c1185 : checkCell pa19 (cellAt 1185) b1185 = true := by decide +kernel

theorem c1186 : checkCell pa19 (cellAt 1186) b1186 = true := by decide +kernel

theorem c1187 : checkCell pa19 (cellAt 1187) b1187 = true := by decide +kernel

theorem c1188 : checkCell pa19 (cellAt 1188) b1188 = true := by decide +kernel

theorem c1189 : checkCell pa19 (cellAt 1189) b1189 = true := by decide +kernel

theorem c1190 : checkCell pa19 (cellAt 1190) b1190 = true := by decide +kernel

theorem c1191 : checkCell pa19 (cellAt 1191) b1191 = true := by decide +kernel

theorem c1192 : checkCell pa19 (cellAt 1192) b1192 = true := by decide +kernel

theorem c1193 : checkCell pa19 (cellAt 1193) b1193 = true := by decide +kernel

theorem c1194 : checkCell pa19 (cellAt 1194) b1194 = true := by decide +kernel

theorem slice1185 : slice 1185 10 = [cellAt 1185, cellAt 1186, cellAt 1187, cellAt 1188, cellAt 1189, cellAt 1190, cellAt 1191, cellAt 1192, cellAt 1193, cellAt 1194] := by decide +kernel

theorem batch1185_ok : checkAll pa19 (slice 1185 10) breaks1185 = true := by
  rw [slice1185]
  simp only [breaks1185, checkAll, c1185, c1186, c1187, c1188, c1189, c1190, c1191, c1192, c1193, c1194, Bool.and_self]

theorem batch1185 : ∀ c ∈ slice 1185 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1185_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1185
