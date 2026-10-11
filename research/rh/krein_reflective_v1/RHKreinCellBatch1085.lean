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

/-! Serialized cells 1085 to 1094: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1085 : List ℚ := [13125/1024]
def b1086 : List ℚ := [26325/2048]
def b1087 : List ℚ := [52725/4096]
def b1088 : List ℚ := [825/64]
def b1089 : List ℚ := [52875/4096]
def b1090 : List ℚ := [26475/2048]
def b1091 : List ℚ := [53025/4096]
def b1092 : List ℚ := [13275/1024]
def b1093 : List ℚ := [53175/4096]
def b1094 : List ℚ := [26625/2048]

def breaks1085 : List (List ℚ) := [b1085, b1086, b1087, b1088, b1089, b1090, b1091, b1092, b1093, b1094]

theorem c1085 : checkCell pa19 (cellAt 1085) b1085 = true := by decide +kernel

theorem c1086 : checkCell pa19 (cellAt 1086) b1086 = true := by decide +kernel

theorem c1087 : checkCell pa19 (cellAt 1087) b1087 = true := by decide +kernel

theorem c1088 : checkCell pa19 (cellAt 1088) b1088 = true := by decide +kernel

theorem c1089 : checkCell pa19 (cellAt 1089) b1089 = true := by decide +kernel

theorem c1090 : checkCell pa19 (cellAt 1090) b1090 = true := by decide +kernel

theorem c1091 : checkCell pa19 (cellAt 1091) b1091 = true := by decide +kernel

theorem c1092 : checkCell pa19 (cellAt 1092) b1092 = true := by decide +kernel

theorem c1093 : checkCell pa19 (cellAt 1093) b1093 = true := by decide +kernel

theorem c1094 : checkCell pa19 (cellAt 1094) b1094 = true := by decide +kernel

theorem slice1085 : slice 1085 10 = [cellAt 1085, cellAt 1086, cellAt 1087, cellAt 1088, cellAt 1089, cellAt 1090, cellAt 1091, cellAt 1092, cellAt 1093, cellAt 1094] := by decide +kernel

theorem batch1085_ok : checkAll pa19 (slice 1085 10) breaks1085 = true := by
  rw [slice1085]
  simp only [breaks1085, checkAll, c1085, c1086, c1087, c1088, c1089, c1090, c1091, c1092, c1093, c1094, Bool.and_self]

theorem batch1085 : ∀ c ∈ slice 1085 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1085_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1085
