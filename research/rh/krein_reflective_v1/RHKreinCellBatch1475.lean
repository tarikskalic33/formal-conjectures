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

/-! Serialized cells 1475 to 1484: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1475 : List ℚ := [22575/256]
def b1476 : List ℚ := [11325/128]
def b1477 : List ℚ := [22725/256]
def b1478 : List ℚ := [1425/16]
def b1479 : List ℚ := [22875/256]
def b1480 : List ℚ := [11475/128]
def b1481 : List ℚ := [23025/256]
def b1482 : List ℚ := [5775/64]
def b1483 : List ℚ := [23175/256]
def b1484 : List ℚ := [46425/512, 11625/128]

def breaks1475 : List (List ℚ) := [b1475, b1476, b1477, b1478, b1479, b1480, b1481, b1482, b1483, b1484]

theorem c1475 : checkCell pa19 (cellAt 1475) b1475 = true := by decide +kernel

theorem c1476 : checkCell pa19 (cellAt 1476) b1476 = true := by decide +kernel

theorem c1477 : checkCell pa19 (cellAt 1477) b1477 = true := by decide +kernel

theorem c1478 : checkCell pa19 (cellAt 1478) b1478 = true := by decide +kernel

theorem c1479 : checkCell pa19 (cellAt 1479) b1479 = true := by decide +kernel

theorem c1480 : checkCell pa19 (cellAt 1480) b1480 = true := by decide +kernel

theorem c1481 : checkCell pa19 (cellAt 1481) b1481 = true := by decide +kernel

theorem c1482 : checkCell pa19 (cellAt 1482) b1482 = true := by decide +kernel

theorem c1483 : checkCell pa19 (cellAt 1483) b1483 = true := by decide +kernel

theorem c1484 : checkCell pa19 (cellAt 1484) b1484 = true := by decide +kernel

theorem slice1475 : slice 1475 10 = [cellAt 1475, cellAt 1476, cellAt 1477, cellAt 1478, cellAt 1479, cellAt 1480, cellAt 1481, cellAt 1482, cellAt 1483, cellAt 1484] := by decide +kernel

theorem batch1475_ok : checkAll pa19 (slice 1475 10) breaks1475 = true := by
  rw [slice1475]
  simp only [breaks1475, checkAll, c1475, c1476, c1477, c1478, c1479, c1480, c1481, c1482, c1483, c1484, Bool.and_self]

theorem batch1475 : ∀ c ∈ slice 1475 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1475_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1475
