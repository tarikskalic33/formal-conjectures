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

/-! Serialized cells 1445 to 1454: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1445 : List ℚ := [20325/256]
def b1446 : List ℚ := [1275/16]
def b1447 : List ℚ := [20475/256]
def b1448 : List ℚ := [10275/128]
def b1449 : List ℚ := [20625/256]
def b1450 : List ℚ := [5175/64]
def b1451 : List ℚ := [20775/256]
def b1452 : List ℚ := [10425/128]
def b1453 : List ℚ := [20925/256]
def b1454 : List ℚ := [41925/512, 2625/32]

def breaks1445 : List (List ℚ) := [b1445, b1446, b1447, b1448, b1449, b1450, b1451, b1452, b1453, b1454]

theorem c1445 : checkCell pa19 (cellAt 1445) b1445 = true := by decide +kernel

theorem c1446 : checkCell pa19 (cellAt 1446) b1446 = true := by decide +kernel

theorem c1447 : checkCell pa19 (cellAt 1447) b1447 = true := by decide +kernel

theorem c1448 : checkCell pa19 (cellAt 1448) b1448 = true := by decide +kernel

theorem c1449 : checkCell pa19 (cellAt 1449) b1449 = true := by decide +kernel

theorem c1450 : checkCell pa19 (cellAt 1450) b1450 = true := by decide +kernel

theorem c1451 : checkCell pa19 (cellAt 1451) b1451 = true := by decide +kernel

theorem c1452 : checkCell pa19 (cellAt 1452) b1452 = true := by decide +kernel

theorem c1453 : checkCell pa19 (cellAt 1453) b1453 = true := by decide +kernel

theorem c1454 : checkCell pa19 (cellAt 1454) b1454 = true := by decide +kernel

theorem slice1445 : slice 1445 10 = [cellAt 1445, cellAt 1446, cellAt 1447, cellAt 1448, cellAt 1449, cellAt 1450, cellAt 1451, cellAt 1452, cellAt 1453, cellAt 1454] := by decide +kernel

theorem batch1445_ok : checkAll pa19 (slice 1445 10) breaks1445 = true := by
  rw [slice1445]
  simp only [breaks1445, checkAll, c1445, c1446, c1447, c1448, c1449, c1450, c1451, c1452, c1453, c1454, Bool.and_self]

theorem batch1445 : ∀ c ∈ slice 1445 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1445_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1445
