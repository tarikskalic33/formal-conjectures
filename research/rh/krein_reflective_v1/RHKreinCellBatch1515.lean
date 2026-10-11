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

/-! Serialized cells 1515 to 1524: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1515 : List ℚ := [25575/256]
def b1516 : List ℚ := [12825/128]
def b1517 : List ℚ := [25725/256]
def b1518 : List ℚ := [3225/32]
def b1519 : List ℚ := [25875/256]
def b1520 : List ℚ := [12975/128]
def b1521 : List ℚ := [26025/256]
def b1522 : List ℚ := [6525/64]
def b1523 : List ℚ := [26175/256]
def b1524 : List ℚ := [13125/128]

def breaks1515 : List (List ℚ) := [b1515, b1516, b1517, b1518, b1519, b1520, b1521, b1522, b1523, b1524]

theorem c1515 : checkCell pa19 (cellAt 1515) b1515 = true := by decide +kernel

theorem c1516 : checkCell pa19 (cellAt 1516) b1516 = true := by decide +kernel

theorem c1517 : checkCell pa19 (cellAt 1517) b1517 = true := by decide +kernel

theorem c1518 : checkCell pa19 (cellAt 1518) b1518 = true := by decide +kernel

theorem c1519 : checkCell pa19 (cellAt 1519) b1519 = true := by decide +kernel

theorem c1520 : checkCell pa19 (cellAt 1520) b1520 = true := by decide +kernel

theorem c1521 : checkCell pa19 (cellAt 1521) b1521 = true := by decide +kernel

theorem c1522 : checkCell pa19 (cellAt 1522) b1522 = true := by decide +kernel

theorem c1523 : checkCell pa19 (cellAt 1523) b1523 = true := by decide +kernel

theorem c1524 : checkCell pa19 (cellAt 1524) b1524 = true := by decide +kernel

theorem slice1515 : slice 1515 10 = [cellAt 1515, cellAt 1516, cellAt 1517, cellAt 1518, cellAt 1519, cellAt 1520, cellAt 1521, cellAt 1522, cellAt 1523, cellAt 1524] := by decide +kernel

theorem batch1515_ok : checkAll pa19 (slice 1515 10) breaks1515 = true := by
  rw [slice1515]
  simp only [breaks1515, checkAll, c1515, c1516, c1517, c1518, c1519, c1520, c1521, c1522, c1523, c1524, Bool.and_self]

theorem batch1515 : ∀ c ∈ slice 1515 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1515_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1515
