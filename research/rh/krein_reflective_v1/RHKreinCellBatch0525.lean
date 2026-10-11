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

/-! Serialized cells 525 to 534: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0525 : List ℚ := [40875/32768]
def b0526 : List ℚ := [20475/16384]
def b0527 : List ℚ := [41025/32768]
def b0528 : List ℚ := [10275/8192]
def b0529 : List ℚ := [20625/16384]
def b0530 : List ℚ := [5175/4096]
def b0531 : List ℚ := [20775/16384]
def b0532 : List ℚ := [10425/8192]
def b0533 : List ℚ := [20925/16384]
def b0534 : List ℚ := [2625/2048]

def breaks0525 : List (List ℚ) := [b0525, b0526, b0527, b0528, b0529, b0530, b0531, b0532, b0533, b0534]

theorem c0525 : checkCell pa19 (cellAt 525) b0525 = true := by decide +kernel

theorem c0526 : checkCell pa19 (cellAt 526) b0526 = true := by decide +kernel

theorem c0527 : checkCell pa19 (cellAt 527) b0527 = true := by decide +kernel

theorem c0528 : checkCell pa19 (cellAt 528) b0528 = true := by decide +kernel

theorem c0529 : checkCell pa19 (cellAt 529) b0529 = true := by decide +kernel

theorem c0530 : checkCell pa19 (cellAt 530) b0530 = true := by decide +kernel

theorem c0531 : checkCell pa19 (cellAt 531) b0531 = true := by decide +kernel

theorem c0532 : checkCell pa19 (cellAt 532) b0532 = true := by decide +kernel

theorem c0533 : checkCell pa19 (cellAt 533) b0533 = true := by decide +kernel

theorem c0534 : checkCell pa19 (cellAt 534) b0534 = true := by decide +kernel

theorem slice0525 : slice 525 10 = [cellAt 525, cellAt 526, cellAt 527, cellAt 528, cellAt 529, cellAt 530, cellAt 531, cellAt 532, cellAt 533, cellAt 534] := by decide +kernel

theorem batch0525_ok : checkAll pa19 (slice 525 10) breaks0525 = true := by
  rw [slice0525]
  simp only [breaks0525, checkAll, c0525, c0526, c0527, c0528, c0529, c0530, c0531, c0532, c0533, c0534, Bool.and_self]

theorem batch0525 : ∀ c ∈ slice 525 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0525_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0525
