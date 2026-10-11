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

/-! Serialized cells 1685 to 1694: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1685 : List ℚ := [38325/256]
def b1686 : List ℚ := [150]
def b1687 : List ℚ := [38475/256]
def b1688 : List ℚ := [19275/128]
def b1689 : List ℚ := [38625/256]
def b1690 : List ℚ := [9675/64]
def b1691 : List ℚ := [38775/256]
def b1692 : List ℚ := [19425/128]
def b1693 : List ℚ := [38925/256]
def b1694 : List ℚ := [4875/32]

def breaks1685 : List (List ℚ) := [b1685, b1686, b1687, b1688, b1689, b1690, b1691, b1692, b1693, b1694]

theorem c1685 : checkCell pa19 (cellAt 1685) b1685 = true := by decide +kernel

theorem c1686 : checkCell pa19 (cellAt 1686) b1686 = true := by decide +kernel

theorem c1687 : checkCell pa19 (cellAt 1687) b1687 = true := by decide +kernel

theorem c1688 : checkCell pa19 (cellAt 1688) b1688 = true := by decide +kernel

theorem c1689 : checkCell pa19 (cellAt 1689) b1689 = true := by decide +kernel

theorem c1690 : checkCell pa19 (cellAt 1690) b1690 = true := by decide +kernel

theorem c1691 : checkCell pa19 (cellAt 1691) b1691 = true := by decide +kernel

theorem c1692 : checkCell pa19 (cellAt 1692) b1692 = true := by decide +kernel

theorem c1693 : checkCell pa19 (cellAt 1693) b1693 = true := by decide +kernel

theorem c1694 : checkCell pa19 (cellAt 1694) b1694 = true := by decide +kernel

theorem slice1685 : slice 1685 10 = [cellAt 1685, cellAt 1686, cellAt 1687, cellAt 1688, cellAt 1689, cellAt 1690, cellAt 1691, cellAt 1692, cellAt 1693, cellAt 1694] := by decide +kernel

theorem batch1685_ok : checkAll pa19 (slice 1685 10) breaks1685 = true := by
  rw [slice1685]
  simp only [breaks1685, checkAll, c1685, c1686, c1687, c1688, c1689, c1690, c1691, c1692, c1693, c1694, Bool.and_self]

theorem batch1685 : ∀ c ∈ slice 1685 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1685_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1685
