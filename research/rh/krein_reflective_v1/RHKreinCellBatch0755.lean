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

/-! Serialized cells 755 to 764: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0755 : List ℚ := [6375/2048]
def b0756 : List ℚ := [12825/4096]
def b0757 : List ℚ := [3225/1024]
def b0758 : List ℚ := [12975/4096]
def b0759 : List ℚ := [6525/2048]
def b0760 : List ℚ := [13125/4096]
def b0761 : List ℚ := [825/256]
def b0762 : List ℚ := [13275/4096]
def b0763 : List ℚ := [6675/2048]
def b0764 : List ℚ := [13425/4096]

def breaks0755 : List (List ℚ) := [b0755, b0756, b0757, b0758, b0759, b0760, b0761, b0762, b0763, b0764]

theorem c0755 : checkCell pa19 (cellAt 755) b0755 = true := by decide +kernel

theorem c0756 : checkCell pa19 (cellAt 756) b0756 = true := by decide +kernel

theorem c0757 : checkCell pa19 (cellAt 757) b0757 = true := by decide +kernel

theorem c0758 : checkCell pa19 (cellAt 758) b0758 = true := by decide +kernel

theorem c0759 : checkCell pa19 (cellAt 759) b0759 = true := by decide +kernel

theorem c0760 : checkCell pa19 (cellAt 760) b0760 = true := by decide +kernel

theorem c0761 : checkCell pa19 (cellAt 761) b0761 = true := by decide +kernel

theorem c0762 : checkCell pa19 (cellAt 762) b0762 = true := by decide +kernel

theorem c0763 : checkCell pa19 (cellAt 763) b0763 = true := by decide +kernel

theorem c0764 : checkCell pa19 (cellAt 764) b0764 = true := by decide +kernel

theorem slice0755 : slice 755 10 = [cellAt 755, cellAt 756, cellAt 757, cellAt 758, cellAt 759, cellAt 760, cellAt 761, cellAt 762, cellAt 763, cellAt 764] := by decide +kernel

theorem batch0755_ok : checkAll pa19 (slice 755 10) breaks0755 = true := by
  rw [slice0755]
  simp only [breaks0755, checkAll, c0755, c0756, c0757, c0758, c0759, c0760, c0761, c0762, c0763, c0764, Bool.and_self]

theorem batch0755 : ∀ c ∈ slice 755 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0755_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0755
