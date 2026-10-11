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

/-! Serialized cells 1635 to 1644: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1635 : List ℚ := [34575/256]
def b1636 : List ℚ := [17325/128]
def b1637 : List ℚ := [34725/256]
def b1638 : List ℚ := [2175/16]
def b1639 : List ℚ := [69675/512, 34875/256]
def b1640 : List ℚ := [69825/512, 17475/128]
def b1641 : List ℚ := [69975/512, 35025/256]
def b1642 : List ℚ := [70125/512, 8775/64]
def b1643 : List ℚ := [70275/512, 35175/256]
def b1644 : List ℚ := [70425/512, 17625/128]

def breaks1635 : List (List ℚ) := [b1635, b1636, b1637, b1638, b1639, b1640, b1641, b1642, b1643, b1644]

theorem c1635 : checkCell pa19 (cellAt 1635) b1635 = true := by decide +kernel

theorem c1636 : checkCell pa19 (cellAt 1636) b1636 = true := by decide +kernel

theorem c1637 : checkCell pa19 (cellAt 1637) b1637 = true := by decide +kernel

theorem c1638 : checkCell pa19 (cellAt 1638) b1638 = true := by decide +kernel

theorem c1639 : checkCell pa19 (cellAt 1639) b1639 = true := by decide +kernel

theorem c1640 : checkCell pa19 (cellAt 1640) b1640 = true := by decide +kernel

theorem c1641 : checkCell pa19 (cellAt 1641) b1641 = true := by decide +kernel

theorem c1642 : checkCell pa19 (cellAt 1642) b1642 = true := by decide +kernel

theorem c1643 : checkCell pa19 (cellAt 1643) b1643 = true := by decide +kernel

theorem c1644 : checkCell pa19 (cellAt 1644) b1644 = true := by decide +kernel

theorem slice1635 : slice 1635 10 = [cellAt 1635, cellAt 1636, cellAt 1637, cellAt 1638, cellAt 1639, cellAt 1640, cellAt 1641, cellAt 1642, cellAt 1643, cellAt 1644] := by decide +kernel

theorem batch1635_ok : checkAll pa19 (slice 1635 10) breaks1635 = true := by
  rw [slice1635]
  simp only [breaks1635, checkAll, c1635, c1636, c1637, c1638, c1639, c1640, c1641, c1642, c1643, c1644, Bool.and_self]

theorem batch1635 : ∀ c ∈ slice 1635 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1635_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1635
