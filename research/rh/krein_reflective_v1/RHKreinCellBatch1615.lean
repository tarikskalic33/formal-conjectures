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

/-! Serialized cells 1615 to 1624: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1615 : List ℚ := [66075/512, 33075/256]
def b1616 : List ℚ := [16575/128]
def b1617 : List ℚ := [33225/256]
def b1618 : List ℚ := [8325/64]
def b1619 : List ℚ := [33375/256]
def b1620 : List ℚ := [16725/128]
def b1621 : List ℚ := [33525/256]
def b1622 : List ℚ := [525/4]
def b1623 : List ℚ := [33675/256]
def b1624 : List ℚ := [16875/128]

def breaks1615 : List (List ℚ) := [b1615, b1616, b1617, b1618, b1619, b1620, b1621, b1622, b1623, b1624]

theorem c1615 : checkCell pa19 (cellAt 1615) b1615 = true := by decide +kernel

theorem c1616 : checkCell pa19 (cellAt 1616) b1616 = true := by decide +kernel

theorem c1617 : checkCell pa19 (cellAt 1617) b1617 = true := by decide +kernel

theorem c1618 : checkCell pa19 (cellAt 1618) b1618 = true := by decide +kernel

theorem c1619 : checkCell pa19 (cellAt 1619) b1619 = true := by decide +kernel

theorem c1620 : checkCell pa19 (cellAt 1620) b1620 = true := by decide +kernel

theorem c1621 : checkCell pa19 (cellAt 1621) b1621 = true := by decide +kernel

theorem c1622 : checkCell pa19 (cellAt 1622) b1622 = true := by decide +kernel

theorem c1623 : checkCell pa19 (cellAt 1623) b1623 = true := by decide +kernel

theorem c1624 : checkCell pa19 (cellAt 1624) b1624 = true := by decide +kernel

theorem slice1615 : slice 1615 10 = [cellAt 1615, cellAt 1616, cellAt 1617, cellAt 1618, cellAt 1619, cellAt 1620, cellAt 1621, cellAt 1622, cellAt 1623, cellAt 1624] := by decide +kernel

theorem batch1615_ok : checkAll pa19 (slice 1615 10) breaks1615 = true := by
  rw [slice1615]
  simp only [breaks1615, checkAll, c1615, c1616, c1617, c1618, c1619, c1620, c1621, c1622, c1623, c1624, Bool.and_self]

theorem batch1615 : ∀ c ∈ slice 1615 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1615_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1615
