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

/-! Serialized cells 1675 to 1684: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1675 : List ℚ := [37575/256]
def b1676 : List ℚ := [18825/128]
def b1677 : List ℚ := [37725/256]
def b1678 : List ℚ := [4725/32]
def b1679 : List ℚ := [37875/256]
def b1680 : List ℚ := [18975/128]
def b1681 : List ℚ := [38025/256]
def b1682 : List ℚ := [9525/64]
def b1683 : List ℚ := [38175/256]
def b1684 : List ℚ := [19125/128]

def breaks1675 : List (List ℚ) := [b1675, b1676, b1677, b1678, b1679, b1680, b1681, b1682, b1683, b1684]

theorem c1675 : checkCell pa19 (cellAt 1675) b1675 = true := by decide +kernel

theorem c1676 : checkCell pa19 (cellAt 1676) b1676 = true := by decide +kernel

theorem c1677 : checkCell pa19 (cellAt 1677) b1677 = true := by decide +kernel

theorem c1678 : checkCell pa19 (cellAt 1678) b1678 = true := by decide +kernel

theorem c1679 : checkCell pa19 (cellAt 1679) b1679 = true := by decide +kernel

theorem c1680 : checkCell pa19 (cellAt 1680) b1680 = true := by decide +kernel

theorem c1681 : checkCell pa19 (cellAt 1681) b1681 = true := by decide +kernel

theorem c1682 : checkCell pa19 (cellAt 1682) b1682 = true := by decide +kernel

theorem c1683 : checkCell pa19 (cellAt 1683) b1683 = true := by decide +kernel

theorem c1684 : checkCell pa19 (cellAt 1684) b1684 = true := by decide +kernel

theorem slice1675 : slice 1675 10 = [cellAt 1675, cellAt 1676, cellAt 1677, cellAt 1678, cellAt 1679, cellAt 1680, cellAt 1681, cellAt 1682, cellAt 1683, cellAt 1684] := by decide +kernel

theorem batch1675_ok : checkAll pa19 (slice 1675 10) breaks1675 = true := by
  rw [slice1675]
  simp only [breaks1675, checkAll, c1675, c1676, c1677, c1678, c1679, c1680, c1681, c1682, c1683, c1684, Bool.and_self]

theorem batch1675 : ∀ c ∈ slice 1675 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1675_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1675
