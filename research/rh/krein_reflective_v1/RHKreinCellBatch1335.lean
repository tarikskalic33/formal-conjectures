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

/-! Serialized cells 1335 to 1344: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1335 : List ℚ := [12075/256]
def b1336 : List ℚ := [6075/128]
def b1337 : List ℚ := [12225/256]
def b1338 : List ℚ := [3075/64]
def b1339 : List ℚ := [12375/256]
def b1340 : List ℚ := [6225/128]
def b1341 : List ℚ := [12525/256]
def b1342 : List ℚ := [1575/32]
def b1343 : List ℚ := [12675/256]
def b1344 : List ℚ := [6375/128]

def breaks1335 : List (List ℚ) := [b1335, b1336, b1337, b1338, b1339, b1340, b1341, b1342, b1343, b1344]

theorem c1335 : checkCell pa19 (cellAt 1335) b1335 = true := by decide +kernel

theorem c1336 : checkCell pa19 (cellAt 1336) b1336 = true := by decide +kernel

theorem c1337 : checkCell pa19 (cellAt 1337) b1337 = true := by decide +kernel

theorem c1338 : checkCell pa19 (cellAt 1338) b1338 = true := by decide +kernel

theorem c1339 : checkCell pa19 (cellAt 1339) b1339 = true := by decide +kernel

theorem c1340 : checkCell pa19 (cellAt 1340) b1340 = true := by decide +kernel

theorem c1341 : checkCell pa19 (cellAt 1341) b1341 = true := by decide +kernel

theorem c1342 : checkCell pa19 (cellAt 1342) b1342 = true := by decide +kernel

theorem c1343 : checkCell pa19 (cellAt 1343) b1343 = true := by decide +kernel

theorem c1344 : checkCell pa19 (cellAt 1344) b1344 = true := by decide +kernel

theorem slice1335 : slice 1335 10 = [cellAt 1335, cellAt 1336, cellAt 1337, cellAt 1338, cellAt 1339, cellAt 1340, cellAt 1341, cellAt 1342, cellAt 1343, cellAt 1344] := by decide +kernel

theorem batch1335_ok : checkAll pa19 (slice 1335 10) breaks1335 = true := by
  rw [slice1335]
  simp only [breaks1335, checkAll, c1335, c1336, c1337, c1338, c1339, c1340, c1341, c1342, c1343, c1344, Bool.and_self]

theorem batch1335 : ∀ c ∈ slice 1335 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1335_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1335
