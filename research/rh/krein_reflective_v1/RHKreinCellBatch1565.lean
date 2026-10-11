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

/-! Serialized cells 1565 to 1574: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1565 : List ℚ := [29325/256]
def b1566 : List ℚ := [3675/32]
def b1567 : List ℚ := [29475/256]
def b1568 : List ℚ := [14775/128]
def b1569 : List ℚ := [29625/256]
def b1570 : List ℚ := [7425/64]
def b1571 : List ℚ := [29775/256]
def b1572 : List ℚ := [14925/128]
def b1573 : List ℚ := [29925/256]
def b1574 : List ℚ := [1875/16]

def breaks1565 : List (List ℚ) := [b1565, b1566, b1567, b1568, b1569, b1570, b1571, b1572, b1573, b1574]

theorem c1565 : checkCell pa19 (cellAt 1565) b1565 = true := by decide +kernel

theorem c1566 : checkCell pa19 (cellAt 1566) b1566 = true := by decide +kernel

theorem c1567 : checkCell pa19 (cellAt 1567) b1567 = true := by decide +kernel

theorem c1568 : checkCell pa19 (cellAt 1568) b1568 = true := by decide +kernel

theorem c1569 : checkCell pa19 (cellAt 1569) b1569 = true := by decide +kernel

theorem c1570 : checkCell pa19 (cellAt 1570) b1570 = true := by decide +kernel

theorem c1571 : checkCell pa19 (cellAt 1571) b1571 = true := by decide +kernel

theorem c1572 : checkCell pa19 (cellAt 1572) b1572 = true := by decide +kernel

theorem c1573 : checkCell pa19 (cellAt 1573) b1573 = true := by decide +kernel

theorem c1574 : checkCell pa19 (cellAt 1574) b1574 = true := by decide +kernel

theorem slice1565 : slice 1565 10 = [cellAt 1565, cellAt 1566, cellAt 1567, cellAt 1568, cellAt 1569, cellAt 1570, cellAt 1571, cellAt 1572, cellAt 1573, cellAt 1574] := by decide +kernel

theorem batch1565_ok : checkAll pa19 (slice 1565 10) breaks1565 = true := by
  rw [slice1565]
  simp only [breaks1565, checkAll, c1565, c1566, c1567, c1568, c1569, c1570, c1571, c1572, c1573, c1574, Bool.and_self]

theorem batch1565 : ∀ c ∈ slice 1565 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1565_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1565
