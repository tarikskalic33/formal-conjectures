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

/-! Serialized cells 575 to 584: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0575 : List ℚ := [24075/16384]
def b0576 : List ℚ := [12075/8192]
def b0577 : List ℚ := [24225/16384]
def b0578 : List ℚ := [6075/4096]
def b0579 : List ℚ := [24375/16384]
def b0580 : List ℚ := [12225/8192]
def b0581 : List ℚ := [24525/16384]
def b0582 : List ℚ := [3075/2048]
def b0583 : List ℚ := [24675/16384]
def b0584 : List ℚ := [12375/8192]

def breaks0575 : List (List ℚ) := [b0575, b0576, b0577, b0578, b0579, b0580, b0581, b0582, b0583, b0584]

theorem c0575 : checkCell pa19 (cellAt 575) b0575 = true := by decide +kernel

theorem c0576 : checkCell pa19 (cellAt 576) b0576 = true := by decide +kernel

theorem c0577 : checkCell pa19 (cellAt 577) b0577 = true := by decide +kernel

theorem c0578 : checkCell pa19 (cellAt 578) b0578 = true := by decide +kernel

theorem c0579 : checkCell pa19 (cellAt 579) b0579 = true := by decide +kernel

theorem c0580 : checkCell pa19 (cellAt 580) b0580 = true := by decide +kernel

theorem c0581 : checkCell pa19 (cellAt 581) b0581 = true := by decide +kernel

theorem c0582 : checkCell pa19 (cellAt 582) b0582 = true := by decide +kernel

theorem c0583 : checkCell pa19 (cellAt 583) b0583 = true := by decide +kernel

theorem c0584 : checkCell pa19 (cellAt 584) b0584 = true := by decide +kernel

theorem slice0575 : slice 575 10 = [cellAt 575, cellAt 576, cellAt 577, cellAt 578, cellAt 579, cellAt 580, cellAt 581, cellAt 582, cellAt 583, cellAt 584] := by decide +kernel

theorem batch0575_ok : checkAll pa19 (slice 575 10) breaks0575 = true := by
  rw [slice0575]
  simp only [breaks0575, checkAll, c0575, c0576, c0577, c0578, c0579, c0580, c0581, c0582, c0583, c0584, Bool.and_self]

theorem batch0575 : ∀ c ∈ slice 575 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0575_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0575
