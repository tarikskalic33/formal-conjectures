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

/-! Serialized cells 1695 to 1704: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1695 : List ℚ := [39075/256]
def b1696 : List ℚ := [19575/128]
def b1697 : List ℚ := [39225/256]
def b1698 : List ℚ := [9825/64]
def b1699 : List ℚ := [39375/256]
def b1700 : List ℚ := [19725/128]
def b1701 : List ℚ := [39525/256]
def b1702 : List ℚ := [2475/16]
def b1703 : List ℚ := [39675/256]
def b1704 : List ℚ := [19875/128]

def breaks1695 : List (List ℚ) := [b1695, b1696, b1697, b1698, b1699, b1700, b1701, b1702, b1703, b1704]

theorem c1695 : checkCell pa19 (cellAt 1695) b1695 = true := by decide +kernel

theorem c1696 : checkCell pa19 (cellAt 1696) b1696 = true := by decide +kernel

theorem c1697 : checkCell pa19 (cellAt 1697) b1697 = true := by decide +kernel

theorem c1698 : checkCell pa19 (cellAt 1698) b1698 = true := by decide +kernel

theorem c1699 : checkCell pa19 (cellAt 1699) b1699 = true := by decide +kernel

theorem c1700 : checkCell pa19 (cellAt 1700) b1700 = true := by decide +kernel

theorem c1701 : checkCell pa19 (cellAt 1701) b1701 = true := by decide +kernel

theorem c1702 : checkCell pa19 (cellAt 1702) b1702 = true := by decide +kernel

theorem c1703 : checkCell pa19 (cellAt 1703) b1703 = true := by decide +kernel

theorem c1704 : checkCell pa19 (cellAt 1704) b1704 = true := by decide +kernel

theorem slice1695 : slice 1695 10 = [cellAt 1695, cellAt 1696, cellAt 1697, cellAt 1698, cellAt 1699, cellAt 1700, cellAt 1701, cellAt 1702, cellAt 1703, cellAt 1704] := by decide +kernel

theorem batch1695_ok : checkAll pa19 (slice 1695 10) breaks1695 = true := by
  rw [slice1695]
  simp only [breaks1695, checkAll, c1695, c1696, c1697, c1698, c1699, c1700, c1701, c1702, c1703, c1704, Bool.and_self]

theorem batch1695 : ∀ c ∈ slice 1695 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1695_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1695
