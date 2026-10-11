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

/-! Serialized cells 1715 to 1724: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1715 : List ℚ := [40575/256]
def b1716 : List ℚ := [20325/128]
def b1717 : List ℚ := [40725/256]
def b1718 : List ℚ := [1275/8]
def b1719 : List ℚ := [40875/256]
def b1720 : List ℚ := [20475/128]
def b1721 : List ℚ := [41025/256]
def b1722 : List ℚ := [10275/64]
def b1723 : List ℚ := [41175/256]
def b1724 : List ℚ := [20625/128]

def breaks1715 : List (List ℚ) := [b1715, b1716, b1717, b1718, b1719, b1720, b1721, b1722, b1723, b1724]

theorem c1715 : checkCell pa19 (cellAt 1715) b1715 = true := by decide +kernel

theorem c1716 : checkCell pa19 (cellAt 1716) b1716 = true := by decide +kernel

theorem c1717 : checkCell pa19 (cellAt 1717) b1717 = true := by decide +kernel

theorem c1718 : checkCell pa19 (cellAt 1718) b1718 = true := by decide +kernel

theorem c1719 : checkCell pa19 (cellAt 1719) b1719 = true := by decide +kernel

theorem c1720 : checkCell pa19 (cellAt 1720) b1720 = true := by decide +kernel

theorem c1721 : checkCell pa19 (cellAt 1721) b1721 = true := by decide +kernel

theorem c1722 : checkCell pa19 (cellAt 1722) b1722 = true := by decide +kernel

theorem c1723 : checkCell pa19 (cellAt 1723) b1723 = true := by decide +kernel

theorem c1724 : checkCell pa19 (cellAt 1724) b1724 = true := by decide +kernel

theorem slice1715 : slice 1715 10 = [cellAt 1715, cellAt 1716, cellAt 1717, cellAt 1718, cellAt 1719, cellAt 1720, cellAt 1721, cellAt 1722, cellAt 1723, cellAt 1724] := by decide +kernel

theorem batch1715_ok : checkAll pa19 (slice 1715 10) breaks1715 = true := by
  rw [slice1715]
  simp only [breaks1715, checkAll, c1715, c1716, c1717, c1718, c1719, c1720, c1721, c1722, c1723, c1724, Bool.and_self]

theorem batch1715 : ∀ c ∈ slice 1715 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1715_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1715
