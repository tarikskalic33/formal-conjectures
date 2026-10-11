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

/-! Serialized cells 1645 to 1654: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1645 : List ℚ := [70575/512, 35325/256]
def b1646 : List ℚ := [4425/32]
def b1647 : List ℚ := [35475/256]
def b1648 : List ℚ := [17775/128]
def b1649 : List ℚ := [35625/256]
def b1650 : List ℚ := [8925/64]
def b1651 : List ℚ := [35775/256]
def b1652 : List ℚ := [17925/128]
def b1653 : List ℚ := [35925/256]
def b1654 : List ℚ := [1125/8]

def breaks1645 : List (List ℚ) := [b1645, b1646, b1647, b1648, b1649, b1650, b1651, b1652, b1653, b1654]

theorem c1645 : checkCell pa19 (cellAt 1645) b1645 = true := by decide +kernel

theorem c1646 : checkCell pa19 (cellAt 1646) b1646 = true := by decide +kernel

theorem c1647 : checkCell pa19 (cellAt 1647) b1647 = true := by decide +kernel

theorem c1648 : checkCell pa19 (cellAt 1648) b1648 = true := by decide +kernel

theorem c1649 : checkCell pa19 (cellAt 1649) b1649 = true := by decide +kernel

theorem c1650 : checkCell pa19 (cellAt 1650) b1650 = true := by decide +kernel

theorem c1651 : checkCell pa19 (cellAt 1651) b1651 = true := by decide +kernel

theorem c1652 : checkCell pa19 (cellAt 1652) b1652 = true := by decide +kernel

theorem c1653 : checkCell pa19 (cellAt 1653) b1653 = true := by decide +kernel

theorem c1654 : checkCell pa19 (cellAt 1654) b1654 = true := by decide +kernel

theorem slice1645 : slice 1645 10 = [cellAt 1645, cellAt 1646, cellAt 1647, cellAt 1648, cellAt 1649, cellAt 1650, cellAt 1651, cellAt 1652, cellAt 1653, cellAt 1654] := by decide +kernel

theorem batch1645_ok : checkAll pa19 (slice 1645 10) breaks1645 = true := by
  rw [slice1645]
  simp only [breaks1645, checkAll, c1645, c1646, c1647, c1648, c1649, c1650, c1651, c1652, c1653, c1654, Bool.and_self]

theorem batch1645 : ∀ c ∈ slice 1645 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1645_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1645
