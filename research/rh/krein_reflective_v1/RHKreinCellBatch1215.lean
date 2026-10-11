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

/-! Serialized cells 1215 to 1224: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1215 : List ℚ := [1425/64]
def b1216 : List ℚ := [5775/256]
def b1217 : List ℚ := [2925/128]
def b1218 : List ℚ := [5925/256]
def b1219 : List ℚ := [375/16]
def b1220 : List ℚ := [6075/256]
def b1221 : List ℚ := [3075/128]
def b1222 : List ℚ := [6225/256]
def b1223 : List ℚ := [1575/64]
def b1224 : List ℚ := [6375/256]

def breaks1215 : List (List ℚ) := [b1215, b1216, b1217, b1218, b1219, b1220, b1221, b1222, b1223, b1224]

theorem c1215 : checkCell pa19 (cellAt 1215) b1215 = true := by decide +kernel

theorem c1216 : checkCell pa19 (cellAt 1216) b1216 = true := by decide +kernel

theorem c1217 : checkCell pa19 (cellAt 1217) b1217 = true := by decide +kernel

theorem c1218 : checkCell pa19 (cellAt 1218) b1218 = true := by decide +kernel

theorem c1219 : checkCell pa19 (cellAt 1219) b1219 = true := by decide +kernel

theorem c1220 : checkCell pa19 (cellAt 1220) b1220 = true := by decide +kernel

theorem c1221 : checkCell pa19 (cellAt 1221) b1221 = true := by decide +kernel

theorem c1222 : checkCell pa19 (cellAt 1222) b1222 = true := by decide +kernel

theorem c1223 : checkCell pa19 (cellAt 1223) b1223 = true := by decide +kernel

theorem c1224 : checkCell pa19 (cellAt 1224) b1224 = true := by decide +kernel

theorem slice1215 : slice 1215 10 = [cellAt 1215, cellAt 1216, cellAt 1217, cellAt 1218, cellAt 1219, cellAt 1220, cellAt 1221, cellAt 1222, cellAt 1223, cellAt 1224] := by decide +kernel

theorem batch1215_ok : checkAll pa19 (slice 1215 10) breaks1215 = true := by
  rw [slice1215]
  simp only [breaks1215, checkAll, c1215, c1216, c1217, c1218, c1219, c1220, c1221, c1222, c1223, c1224, Bool.and_self]

theorem batch1215 : ∀ c ∈ slice 1215 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1215_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1215
