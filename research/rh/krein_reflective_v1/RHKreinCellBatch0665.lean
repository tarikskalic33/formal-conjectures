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

/-! Serialized cells 665 to 674: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0665 : List ℚ := [15675/8192]
def b0666 : List ℚ := [7875/4096]
def b0667 : List ℚ := [15825/8192]
def b0668 : List ℚ := [3975/2048]
def b0669 : List ℚ := [15975/8192]
def b0670 : List ℚ := [8025/4096]
def b0671 : List ℚ := [16125/8192]
def b0672 : List ℚ := [2025/1024]
def b0673 : List ℚ := [16275/8192]
def b0674 : List ℚ := [8175/4096]

def breaks0665 : List (List ℚ) := [b0665, b0666, b0667, b0668, b0669, b0670, b0671, b0672, b0673, b0674]

theorem c0665 : checkCell pa19 (cellAt 665) b0665 = true := by decide +kernel

theorem c0666 : checkCell pa19 (cellAt 666) b0666 = true := by decide +kernel

theorem c0667 : checkCell pa19 (cellAt 667) b0667 = true := by decide +kernel

theorem c0668 : checkCell pa19 (cellAt 668) b0668 = true := by decide +kernel

theorem c0669 : checkCell pa19 (cellAt 669) b0669 = true := by decide +kernel

theorem c0670 : checkCell pa19 (cellAt 670) b0670 = true := by decide +kernel

theorem c0671 : checkCell pa19 (cellAt 671) b0671 = true := by decide +kernel

theorem c0672 : checkCell pa19 (cellAt 672) b0672 = true := by decide +kernel

theorem c0673 : checkCell pa19 (cellAt 673) b0673 = true := by decide +kernel

theorem c0674 : checkCell pa19 (cellAt 674) b0674 = true := by decide +kernel

theorem slice0665 : slice 665 10 = [cellAt 665, cellAt 666, cellAt 667, cellAt 668, cellAt 669, cellAt 670, cellAt 671, cellAt 672, cellAt 673, cellAt 674] := by decide +kernel

theorem batch0665_ok : checkAll pa19 (slice 665 10) breaks0665 = true := by
  rw [slice0665]
  simp only [breaks0665, checkAll, c0665, c0666, c0667, c0668, c0669, c0670, c0671, c0672, c0673, c0674, Bool.and_self]

theorem batch0665 : ∀ c ∈ slice 665 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0665_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0665
