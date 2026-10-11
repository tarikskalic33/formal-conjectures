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

/-! Serialized cells 1135 to 1144: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1135 : List ℚ := [8925/512]
def b1136 : List ℚ := [17925/1024]
def b1137 : List ℚ := [1125/64]
def b1138 : List ℚ := [18075/1024]
def b1139 : List ℚ := [9075/512]
def b1140 : List ℚ := [4575/256]
def b1141 : List ℚ := [2325/128]
def b1142 : List ℚ := [9375/512]
def b1143 : List ℚ := [4725/256]
def b1144 : List ℚ := [18975/1024]

def breaks1135 : List (List ℚ) := [b1135, b1136, b1137, b1138, b1139, b1140, b1141, b1142, b1143, b1144]

theorem c1135 : checkCell pa19 (cellAt 1135) b1135 = true := by decide +kernel

theorem c1136 : checkCell pa19 (cellAt 1136) b1136 = true := by decide +kernel

theorem c1137 : checkCell pa19 (cellAt 1137) b1137 = true := by decide +kernel

theorem c1138 : checkCell pa19 (cellAt 1138) b1138 = true := by decide +kernel

theorem c1139 : checkCell pa19 (cellAt 1139) b1139 = true := by decide +kernel

theorem c1140 : checkCell pa19 (cellAt 1140) b1140 = true := by decide +kernel

theorem c1141 : checkCell pa19 (cellAt 1141) b1141 = true := by decide +kernel

theorem c1142 : checkCell pa19 (cellAt 1142) b1142 = true := by decide +kernel

theorem c1143 : checkCell pa19 (cellAt 1143) b1143 = true := by decide +kernel

theorem c1144 : checkCell pa19 (cellAt 1144) b1144 = true := by decide +kernel

theorem slice1135 : slice 1135 10 = [cellAt 1135, cellAt 1136, cellAt 1137, cellAt 1138, cellAt 1139, cellAt 1140, cellAt 1141, cellAt 1142, cellAt 1143, cellAt 1144] := by decide +kernel

theorem batch1135_ok : checkAll pa19 (slice 1135 10) breaks1135 = true := by
  rw [slice1135]
  simp only [breaks1135, checkAll, c1135, c1136, c1137, c1138, c1139, c1140, c1141, c1142, c1143, c1144, Bool.and_self]

theorem batch1135 : ∀ c ∈ slice 1135 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1135_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1135
