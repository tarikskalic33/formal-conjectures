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

/-! Serialized cells 1285 to 1294: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1285 : List ℚ := [1125/32]
def b1286 : List ℚ := [18075/512]
def b1287 : List ℚ := [36225/1024]
def b1288 : List ℚ := [9075/256]
def b1289 : List ℚ := [36375/1024]
def b1290 : List ℚ := [18225/512]
def b1291 : List ℚ := [36525/1024]
def b1292 : List ℚ := [4575/128]
def b1293 : List ℚ := [36675/1024]
def b1294 : List ℚ := [18375/512]

def breaks1285 : List (List ℚ) := [b1285, b1286, b1287, b1288, b1289, b1290, b1291, b1292, b1293, b1294]

theorem c1285 : checkCell pa19 (cellAt 1285) b1285 = true := by decide +kernel

theorem c1286 : checkCell pa19 (cellAt 1286) b1286 = true := by decide +kernel

theorem c1287 : checkCell pa19 (cellAt 1287) b1287 = true := by decide +kernel

theorem c1288 : checkCell pa19 (cellAt 1288) b1288 = true := by decide +kernel

theorem c1289 : checkCell pa19 (cellAt 1289) b1289 = true := by decide +kernel

theorem c1290 : checkCell pa19 (cellAt 1290) b1290 = true := by decide +kernel

theorem c1291 : checkCell pa19 (cellAt 1291) b1291 = true := by decide +kernel

theorem c1292 : checkCell pa19 (cellAt 1292) b1292 = true := by decide +kernel

theorem c1293 : checkCell pa19 (cellAt 1293) b1293 = true := by decide +kernel

theorem c1294 : checkCell pa19 (cellAt 1294) b1294 = true := by decide +kernel

theorem slice1285 : slice 1285 10 = [cellAt 1285, cellAt 1286, cellAt 1287, cellAt 1288, cellAt 1289, cellAt 1290, cellAt 1291, cellAt 1292, cellAt 1293, cellAt 1294] := by decide +kernel

theorem batch1285_ok : checkAll pa19 (slice 1285 10) breaks1285 = true := by
  rw [slice1285]
  simp only [breaks1285, checkAll, c1285, c1286, c1287, c1288, c1289, c1290, c1291, c1292, c1293, c1294, Bool.and_self]

theorem batch1285 : ∀ c ∈ slice 1285 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1285_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1285
