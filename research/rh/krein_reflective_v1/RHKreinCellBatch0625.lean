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

/-! Serialized cells 625 to 634: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0625 : List ℚ := [27825/16384]
def b0626 : List ℚ := [6975/4096]
def b0627 : List ℚ := [27975/16384]
def b0628 : List ℚ := [14025/8192]
def b0629 : List ℚ := [28125/16384]
def b0630 : List ℚ := [3525/2048]
def b0631 : List ℚ := [28275/16384]
def b0632 : List ℚ := [14175/8192]
def b0633 : List ℚ := [28425/16384]
def b0634 : List ℚ := [7125/4096]

def breaks0625 : List (List ℚ) := [b0625, b0626, b0627, b0628, b0629, b0630, b0631, b0632, b0633, b0634]

theorem c0625 : checkCell pa19 (cellAt 625) b0625 = true := by decide +kernel

theorem c0626 : checkCell pa19 (cellAt 626) b0626 = true := by decide +kernel

theorem c0627 : checkCell pa19 (cellAt 627) b0627 = true := by decide +kernel

theorem c0628 : checkCell pa19 (cellAt 628) b0628 = true := by decide +kernel

theorem c0629 : checkCell pa19 (cellAt 629) b0629 = true := by decide +kernel

theorem c0630 : checkCell pa19 (cellAt 630) b0630 = true := by decide +kernel

theorem c0631 : checkCell pa19 (cellAt 631) b0631 = true := by decide +kernel

theorem c0632 : checkCell pa19 (cellAt 632) b0632 = true := by decide +kernel

theorem c0633 : checkCell pa19 (cellAt 633) b0633 = true := by decide +kernel

theorem c0634 : checkCell pa19 (cellAt 634) b0634 = true := by decide +kernel

theorem slice0625 : slice 625 10 = [cellAt 625, cellAt 626, cellAt 627, cellAt 628, cellAt 629, cellAt 630, cellAt 631, cellAt 632, cellAt 633, cellAt 634] := by decide +kernel

theorem batch0625_ok : checkAll pa19 (slice 625 10) breaks0625 = true := by
  rw [slice0625]
  simp only [breaks0625, checkAll, c0625, c0626, c0627, c0628, c0629, c0630, c0631, c0632, c0633, c0634, Bool.and_self]

theorem batch0625 : ∀ c ∈ slice 625 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0625_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0625
