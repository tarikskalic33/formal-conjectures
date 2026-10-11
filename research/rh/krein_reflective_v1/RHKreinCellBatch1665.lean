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

/-! Serialized cells 1665 to 1674: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1665 : List ℚ := [36825/256]
def b1666 : List ℚ := [9225/64]
def b1667 : List ℚ := [36975/256]
def b1668 : List ℚ := [18525/128]
def b1669 : List ℚ := [37125/256]
def b1670 : List ℚ := [74325/512, 2325/16]
def b1671 : List ℚ := [74475/512, 37275/256]
def b1672 : List ℚ := [149175/1024, 74625/512, 18675/128]
def b1673 : List ℚ := [74775/512, 37425/256]
def b1674 : List ℚ := [9375/64]

def breaks1665 : List (List ℚ) := [b1665, b1666, b1667, b1668, b1669, b1670, b1671, b1672, b1673, b1674]

theorem c1665 : checkCell pa19 (cellAt 1665) b1665 = true := by decide +kernel

theorem c1666 : checkCell pa19 (cellAt 1666) b1666 = true := by decide +kernel

theorem c1667 : checkCell pa19 (cellAt 1667) b1667 = true := by decide +kernel

theorem c1668 : checkCell pa19 (cellAt 1668) b1668 = true := by decide +kernel

theorem c1669 : checkCell pa19 (cellAt 1669) b1669 = true := by decide +kernel

theorem c1670 : checkCell pa19 (cellAt 1670) b1670 = true := by decide +kernel

theorem c1671 : checkCell pa19 (cellAt 1671) b1671 = true := by decide +kernel

theorem c1672 : checkCell pa19 (cellAt 1672) b1672 = true := by decide +kernel

theorem c1673 : checkCell pa19 (cellAt 1673) b1673 = true := by decide +kernel

theorem c1674 : checkCell pa19 (cellAt 1674) b1674 = true := by decide +kernel

theorem slice1665 : slice 1665 10 = [cellAt 1665, cellAt 1666, cellAt 1667, cellAt 1668, cellAt 1669, cellAt 1670, cellAt 1671, cellAt 1672, cellAt 1673, cellAt 1674] := by decide +kernel

theorem batch1665_ok : checkAll pa19 (slice 1665 10) breaks1665 = true := by
  rw [slice1665]
  simp only [breaks1665, checkAll, c1665, c1666, c1667, c1668, c1669, c1670, c1671, c1672, c1673, c1674, Bool.and_self]

theorem batch1665 : ∀ c ∈ slice 1665 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1665_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1665
