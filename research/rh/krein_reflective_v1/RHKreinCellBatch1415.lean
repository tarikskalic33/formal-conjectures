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

/-! Serialized cells 1415 to 1424: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1415 : List ℚ := [18075/256]
def b1416 : List ℚ := [9075/128]
def b1417 : List ℚ := [18225/256]
def b1418 : List ℚ := [4575/64]
def b1419 : List ℚ := [18375/256]
def b1420 : List ℚ := [36825/512, 9225/128]
def b1421 : List ℚ := [36975/512, 18525/256]
def b1422 : List ℚ := [2325/32]
def b1423 : List ℚ := [18675/256]
def b1424 : List ℚ := [9375/128]

def breaks1415 : List (List ℚ) := [b1415, b1416, b1417, b1418, b1419, b1420, b1421, b1422, b1423, b1424]

theorem c1415 : checkCell pa19 (cellAt 1415) b1415 = true := by decide +kernel

theorem c1416 : checkCell pa19 (cellAt 1416) b1416 = true := by decide +kernel

theorem c1417 : checkCell pa19 (cellAt 1417) b1417 = true := by decide +kernel

theorem c1418 : checkCell pa19 (cellAt 1418) b1418 = true := by decide +kernel

theorem c1419 : checkCell pa19 (cellAt 1419) b1419 = true := by decide +kernel

theorem c1420 : checkCell pa19 (cellAt 1420) b1420 = true := by decide +kernel

theorem c1421 : checkCell pa19 (cellAt 1421) b1421 = true := by decide +kernel

theorem c1422 : checkCell pa19 (cellAt 1422) b1422 = true := by decide +kernel

theorem c1423 : checkCell pa19 (cellAt 1423) b1423 = true := by decide +kernel

theorem c1424 : checkCell pa19 (cellAt 1424) b1424 = true := by decide +kernel

theorem slice1415 : slice 1415 10 = [cellAt 1415, cellAt 1416, cellAt 1417, cellAt 1418, cellAt 1419, cellAt 1420, cellAt 1421, cellAt 1422, cellAt 1423, cellAt 1424] := by decide +kernel

theorem batch1415_ok : checkAll pa19 (slice 1415 10) breaks1415 = true := by
  rw [slice1415]
  simp only [breaks1415, checkAll, c1415, c1416, c1417, c1418, c1419, c1420, c1421, c1422, c1423, c1424, Bool.and_self]

theorem batch1415 : ∀ c ∈ slice 1415 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1415_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1415
