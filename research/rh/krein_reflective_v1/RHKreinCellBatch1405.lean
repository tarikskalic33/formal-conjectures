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

/-! Serialized cells 1405 to 1414: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1405 : List ℚ := [17325/256]
def b1406 : List ℚ := [2175/32]
def b1407 : List ℚ := [17475/256]
def b1408 : List ℚ := [8775/128]
def b1409 : List ℚ := [17625/256]
def b1410 : List ℚ := [4425/64]
def b1411 : List ℚ := [17775/256]
def b1412 : List ℚ := [8925/128]
def b1413 : List ℚ := [17925/256]
def b1414 : List ℚ := [1125/16]

def breaks1405 : List (List ℚ) := [b1405, b1406, b1407, b1408, b1409, b1410, b1411, b1412, b1413, b1414]

theorem c1405 : checkCell pa19 (cellAt 1405) b1405 = true := by decide +kernel

theorem c1406 : checkCell pa19 (cellAt 1406) b1406 = true := by decide +kernel

theorem c1407 : checkCell pa19 (cellAt 1407) b1407 = true := by decide +kernel

theorem c1408 : checkCell pa19 (cellAt 1408) b1408 = true := by decide +kernel

theorem c1409 : checkCell pa19 (cellAt 1409) b1409 = true := by decide +kernel

theorem c1410 : checkCell pa19 (cellAt 1410) b1410 = true := by decide +kernel

theorem c1411 : checkCell pa19 (cellAt 1411) b1411 = true := by decide +kernel

theorem c1412 : checkCell pa19 (cellAt 1412) b1412 = true := by decide +kernel

theorem c1413 : checkCell pa19 (cellAt 1413) b1413 = true := by decide +kernel

theorem c1414 : checkCell pa19 (cellAt 1414) b1414 = true := by decide +kernel

theorem slice1405 : slice 1405 10 = [cellAt 1405, cellAt 1406, cellAt 1407, cellAt 1408, cellAt 1409, cellAt 1410, cellAt 1411, cellAt 1412, cellAt 1413, cellAt 1414] := by decide +kernel

theorem batch1405_ok : checkAll pa19 (slice 1405 10) breaks1405 = true := by
  rw [slice1405]
  simp only [breaks1405, checkAll, c1405, c1406, c1407, c1408, c1409, c1410, c1411, c1412, c1413, c1414, Bool.and_self]

theorem batch1405 : ∀ c ∈ slice 1405 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1405_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1405
