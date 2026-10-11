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

/-! Serialized cells 1165 to 1174: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1165 : List ℚ := [39825/2048]
def b1166 : List ℚ := [9975/512]
def b1167 : List ℚ := [39975/2048]
def b1168 : List ℚ := [20025/1024]
def b1169 : List ℚ := [40125/2048]
def b1170 : List ℚ := [80325/4096]
def b1171 : List ℚ := [5025/256]
def b1172 : List ℚ := [80475/4096]
def b1173 : List ℚ := [40275/2048]
def b1174 : List ℚ := [80625/4096]

def breaks1165 : List (List ℚ) := [b1165, b1166, b1167, b1168, b1169, b1170, b1171, b1172, b1173, b1174]

theorem c1165 : checkCell pa19 (cellAt 1165) b1165 = true := by decide +kernel

theorem c1166 : checkCell pa19 (cellAt 1166) b1166 = true := by decide +kernel

theorem c1167 : checkCell pa19 (cellAt 1167) b1167 = true := by decide +kernel

theorem c1168 : checkCell pa19 (cellAt 1168) b1168 = true := by decide +kernel

theorem c1169 : checkCell pa19 (cellAt 1169) b1169 = true := by decide +kernel

theorem c1170 : checkCell pa19 (cellAt 1170) b1170 = true := by decide +kernel

theorem c1171 : checkCell pa19 (cellAt 1171) b1171 = true := by decide +kernel

theorem c1172 : checkCell pa19 (cellAt 1172) b1172 = true := by decide +kernel

theorem c1173 : checkCell pa19 (cellAt 1173) b1173 = true := by decide +kernel

theorem c1174 : checkCell pa19 (cellAt 1174) b1174 = true := by decide +kernel

theorem slice1165 : slice 1165 10 = [cellAt 1165, cellAt 1166, cellAt 1167, cellAt 1168, cellAt 1169, cellAt 1170, cellAt 1171, cellAt 1172, cellAt 1173, cellAt 1174] := by decide +kernel

theorem batch1165_ok : checkAll pa19 (slice 1165 10) breaks1165 = true := by
  rw [slice1165]
  simp only [breaks1165, checkAll, c1165, c1166, c1167, c1168, c1169, c1170, c1171, c1172, c1173, c1174, Bool.and_self]

theorem batch1165 : ∀ c ∈ slice 1165 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1165_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1165
