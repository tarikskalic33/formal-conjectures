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

/-! Serialized cells 535 to 544: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0535 : List ℚ := [21075/16384]
def b0536 : List ℚ := [10575/8192]
def b0537 : List ℚ := [21225/16384]
def b0538 : List ℚ := [5325/4096]
def b0539 : List ℚ := [21375/16384]
def b0540 : List ℚ := [10725/8192]
def b0541 : List ℚ := [21525/16384]
def b0542 : List ℚ := [675/512]
def b0543 : List ℚ := [21675/16384]
def b0544 : List ℚ := [10875/8192]

def breaks0535 : List (List ℚ) := [b0535, b0536, b0537, b0538, b0539, b0540, b0541, b0542, b0543, b0544]

theorem c0535 : checkCell pa19 (cellAt 535) b0535 = true := by decide +kernel

theorem c0536 : checkCell pa19 (cellAt 536) b0536 = true := by decide +kernel

theorem c0537 : checkCell pa19 (cellAt 537) b0537 = true := by decide +kernel

theorem c0538 : checkCell pa19 (cellAt 538) b0538 = true := by decide +kernel

theorem c0539 : checkCell pa19 (cellAt 539) b0539 = true := by decide +kernel

theorem c0540 : checkCell pa19 (cellAt 540) b0540 = true := by decide +kernel

theorem c0541 : checkCell pa19 (cellAt 541) b0541 = true := by decide +kernel

theorem c0542 : checkCell pa19 (cellAt 542) b0542 = true := by decide +kernel

theorem c0543 : checkCell pa19 (cellAt 543) b0543 = true := by decide +kernel

theorem c0544 : checkCell pa19 (cellAt 544) b0544 = true := by decide +kernel

theorem slice0535 : slice 535 10 = [cellAt 535, cellAt 536, cellAt 537, cellAt 538, cellAt 539, cellAt 540, cellAt 541, cellAt 542, cellAt 543, cellAt 544] := by decide +kernel

theorem batch0535_ok : checkAll pa19 (slice 535 10) breaks0535 = true := by
  rw [slice0535]
  simp only [breaks0535, checkAll, c0535, c0536, c0537, c0538, c0539, c0540, c0541, c0542, c0543, c0544, Bool.and_self]

theorem batch0535 : ∀ c ∈ slice 535 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0535_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0535
