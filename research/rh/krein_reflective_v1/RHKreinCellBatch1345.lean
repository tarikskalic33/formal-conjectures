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

/-! Serialized cells 1345 to 1354: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1345 : List ℚ := [12825/256]
def b1346 : List ℚ := [3225/64]
def b1347 : List ℚ := [12975/256]
def b1348 : List ℚ := [6525/128]
def b1349 : List ℚ := [13125/256]
def b1350 : List ℚ := [825/16]
def b1351 : List ℚ := [13275/256]
def b1352 : List ℚ := [6675/128]
def b1353 : List ℚ := [13425/256]
def b1354 : List ℚ := [3375/64]

def breaks1345 : List (List ℚ) := [b1345, b1346, b1347, b1348, b1349, b1350, b1351, b1352, b1353, b1354]

theorem c1345 : checkCell pa19 (cellAt 1345) b1345 = true := by decide +kernel

theorem c1346 : checkCell pa19 (cellAt 1346) b1346 = true := by decide +kernel

theorem c1347 : checkCell pa19 (cellAt 1347) b1347 = true := by decide +kernel

theorem c1348 : checkCell pa19 (cellAt 1348) b1348 = true := by decide +kernel

theorem c1349 : checkCell pa19 (cellAt 1349) b1349 = true := by decide +kernel

theorem c1350 : checkCell pa19 (cellAt 1350) b1350 = true := by decide +kernel

theorem c1351 : checkCell pa19 (cellAt 1351) b1351 = true := by decide +kernel

theorem c1352 : checkCell pa19 (cellAt 1352) b1352 = true := by decide +kernel

theorem c1353 : checkCell pa19 (cellAt 1353) b1353 = true := by decide +kernel

theorem c1354 : checkCell pa19 (cellAt 1354) b1354 = true := by decide +kernel

theorem slice1345 : slice 1345 10 = [cellAt 1345, cellAt 1346, cellAt 1347, cellAt 1348, cellAt 1349, cellAt 1350, cellAt 1351, cellAt 1352, cellAt 1353, cellAt 1354] := by decide +kernel

theorem batch1345_ok : checkAll pa19 (slice 1345 10) breaks1345 = true := by
  rw [slice1345]
  simp only [breaks1345, checkAll, c1345, c1346, c1347, c1348, c1349, c1350, c1351, c1352, c1353, c1354, Bool.and_self]

theorem batch1345 : ∀ c ∈ slice 1345 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1345_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1345
