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

/-! Serialized cells 1115 to 1124: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1115 : List ℚ := [8325/512]
def b1116 : List ℚ := [16725/1024]
def b1117 : List ℚ := [33525/2048]
def b1118 : List ℚ := [525/32]
def b1119 : List ℚ := [33675/2048]
def b1120 : List ℚ := [16875/1024]
def b1121 : List ℚ := [33825/2048]
def b1122 : List ℚ := [8475/512]
def b1123 : List ℚ := [33975/2048]
def b1124 : List ℚ := [17025/1024]

def breaks1115 : List (List ℚ) := [b1115, b1116, b1117, b1118, b1119, b1120, b1121, b1122, b1123, b1124]

theorem c1115 : checkCell pa19 (cellAt 1115) b1115 = true := by decide +kernel

theorem c1116 : checkCell pa19 (cellAt 1116) b1116 = true := by decide +kernel

theorem c1117 : checkCell pa19 (cellAt 1117) b1117 = true := by decide +kernel

theorem c1118 : checkCell pa19 (cellAt 1118) b1118 = true := by decide +kernel

theorem c1119 : checkCell pa19 (cellAt 1119) b1119 = true := by decide +kernel

theorem c1120 : checkCell pa19 (cellAt 1120) b1120 = true := by decide +kernel

theorem c1121 : checkCell pa19 (cellAt 1121) b1121 = true := by decide +kernel

theorem c1122 : checkCell pa19 (cellAt 1122) b1122 = true := by decide +kernel

theorem c1123 : checkCell pa19 (cellAt 1123) b1123 = true := by decide +kernel

theorem c1124 : checkCell pa19 (cellAt 1124) b1124 = true := by decide +kernel

theorem slice1115 : slice 1115 10 = [cellAt 1115, cellAt 1116, cellAt 1117, cellAt 1118, cellAt 1119, cellAt 1120, cellAt 1121, cellAt 1122, cellAt 1123, cellAt 1124] := by decide +kernel

theorem batch1115_ok : checkAll pa19 (slice 1115 10) breaks1115 = true := by
  rw [slice1115]
  simp only [breaks1115, checkAll, c1115, c1116, c1117, c1118, c1119, c1120, c1121, c1122, c1123, c1124, Bool.and_self]

theorem batch1115 : ∀ c ∈ slice 1115 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1115_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1115
