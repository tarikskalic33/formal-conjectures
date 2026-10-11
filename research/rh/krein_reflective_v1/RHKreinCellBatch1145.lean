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

/-! Serialized cells 1145 to 1154: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1145 : List ℚ := [9525/512]
def b1146 : List ℚ := [19125/1024]
def b1147 : List ℚ := [75/4]
def b1148 : List ℚ := [19275/1024]
def b1149 : List ℚ := [38625/2048]
def b1150 : List ℚ := [9675/512]
def b1151 : List ℚ := [38775/2048]
def b1152 : List ℚ := [19425/1024]
def b1153 : List ℚ := [38925/2048]
def b1154 : List ℚ := [4875/256]

def breaks1145 : List (List ℚ) := [b1145, b1146, b1147, b1148, b1149, b1150, b1151, b1152, b1153, b1154]

theorem c1145 : checkCell pa19 (cellAt 1145) b1145 = true := by decide +kernel

theorem c1146 : checkCell pa19 (cellAt 1146) b1146 = true := by decide +kernel

theorem c1147 : checkCell pa19 (cellAt 1147) b1147 = true := by decide +kernel

theorem c1148 : checkCell pa19 (cellAt 1148) b1148 = true := by decide +kernel

theorem c1149 : checkCell pa19 (cellAt 1149) b1149 = true := by decide +kernel

theorem c1150 : checkCell pa19 (cellAt 1150) b1150 = true := by decide +kernel

theorem c1151 : checkCell pa19 (cellAt 1151) b1151 = true := by decide +kernel

theorem c1152 : checkCell pa19 (cellAt 1152) b1152 = true := by decide +kernel

theorem c1153 : checkCell pa19 (cellAt 1153) b1153 = true := by decide +kernel

theorem c1154 : checkCell pa19 (cellAt 1154) b1154 = true := by decide +kernel

theorem slice1145 : slice 1145 10 = [cellAt 1145, cellAt 1146, cellAt 1147, cellAt 1148, cellAt 1149, cellAt 1150, cellAt 1151, cellAt 1152, cellAt 1153, cellAt 1154] := by decide +kernel

theorem batch1145_ok : checkAll pa19 (slice 1145 10) breaks1145 = true := by
  rw [slice1145]
  simp only [breaks1145, checkAll, c1145, c1146, c1147, c1148, c1149, c1150, c1151, c1152, c1153, c1154, Bool.and_self]

theorem batch1145 : ∀ c ∈ slice 1145 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1145_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1145
