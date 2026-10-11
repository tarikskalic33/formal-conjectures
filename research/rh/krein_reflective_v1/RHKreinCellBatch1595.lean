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

/-! Serialized cells 1595 to 1604: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1595 : List ℚ := [31575/256]
def b1596 : List ℚ := [15825/128]
def b1597 : List ℚ := [31725/256]
def b1598 : List ℚ := [3975/32]
def b1599 : List ℚ := [31875/256]
def b1600 : List ℚ := [15975/128]
def b1601 : List ℚ := [32025/256]
def b1602 : List ℚ := [8025/64]
def b1603 : List ℚ := [32175/256]
def b1604 : List ℚ := [16125/128]

def breaks1595 : List (List ℚ) := [b1595, b1596, b1597, b1598, b1599, b1600, b1601, b1602, b1603, b1604]

theorem c1595 : checkCell pa19 (cellAt 1595) b1595 = true := by decide +kernel

theorem c1596 : checkCell pa19 (cellAt 1596) b1596 = true := by decide +kernel

theorem c1597 : checkCell pa19 (cellAt 1597) b1597 = true := by decide +kernel

theorem c1598 : checkCell pa19 (cellAt 1598) b1598 = true := by decide +kernel

theorem c1599 : checkCell pa19 (cellAt 1599) b1599 = true := by decide +kernel

theorem c1600 : checkCell pa19 (cellAt 1600) b1600 = true := by decide +kernel

theorem c1601 : checkCell pa19 (cellAt 1601) b1601 = true := by decide +kernel

theorem c1602 : checkCell pa19 (cellAt 1602) b1602 = true := by decide +kernel

theorem c1603 : checkCell pa19 (cellAt 1603) b1603 = true := by decide +kernel

theorem c1604 : checkCell pa19 (cellAt 1604) b1604 = true := by decide +kernel

theorem slice1595 : slice 1595 10 = [cellAt 1595, cellAt 1596, cellAt 1597, cellAt 1598, cellAt 1599, cellAt 1600, cellAt 1601, cellAt 1602, cellAt 1603, cellAt 1604] := by decide +kernel

theorem batch1595_ok : checkAll pa19 (slice 1595 10) breaks1595 = true := by
  rw [slice1595]
  simp only [breaks1595, checkAll, c1595, c1596, c1597, c1598, c1599, c1600, c1601, c1602, c1603, c1604, Bool.and_self]

theorem batch1595 : ∀ c ∈ slice 1595 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1595_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1595
