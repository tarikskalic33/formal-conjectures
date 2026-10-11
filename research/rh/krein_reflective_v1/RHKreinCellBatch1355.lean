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

/-! Serialized cells 1355 to 1364: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1355 : List ℚ := [13575/256]
def b1356 : List ℚ := [6825/128]
def b1357 : List ℚ := [13725/256]
def b1358 : List ℚ := [1725/32]
def b1359 : List ℚ := [13875/256]
def b1360 : List ℚ := [6975/128]
def b1361 : List ℚ := [14025/256]
def b1362 : List ℚ := [3525/64]
def b1363 : List ℚ := [14175/256]
def b1364 : List ℚ := [7125/128]

def breaks1355 : List (List ℚ) := [b1355, b1356, b1357, b1358, b1359, b1360, b1361, b1362, b1363, b1364]

theorem c1355 : checkCell pa19 (cellAt 1355) b1355 = true := by decide +kernel

theorem c1356 : checkCell pa19 (cellAt 1356) b1356 = true := by decide +kernel

theorem c1357 : checkCell pa19 (cellAt 1357) b1357 = true := by decide +kernel

theorem c1358 : checkCell pa19 (cellAt 1358) b1358 = true := by decide +kernel

theorem c1359 : checkCell pa19 (cellAt 1359) b1359 = true := by decide +kernel

theorem c1360 : checkCell pa19 (cellAt 1360) b1360 = true := by decide +kernel

theorem c1361 : checkCell pa19 (cellAt 1361) b1361 = true := by decide +kernel

theorem c1362 : checkCell pa19 (cellAt 1362) b1362 = true := by decide +kernel

theorem c1363 : checkCell pa19 (cellAt 1363) b1363 = true := by decide +kernel

theorem c1364 : checkCell pa19 (cellAt 1364) b1364 = true := by decide +kernel

theorem slice1355 : slice 1355 10 = [cellAt 1355, cellAt 1356, cellAt 1357, cellAt 1358, cellAt 1359, cellAt 1360, cellAt 1361, cellAt 1362, cellAt 1363, cellAt 1364] := by decide +kernel

theorem batch1355_ok : checkAll pa19 (slice 1355 10) breaks1355 = true := by
  rw [slice1355]
  simp only [breaks1355, checkAll, c1355, c1356, c1357, c1358, c1359, c1360, c1361, c1362, c1363, c1364, Bool.and_self]

theorem batch1355 : ∀ c ∈ slice 1355 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1355_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1355
