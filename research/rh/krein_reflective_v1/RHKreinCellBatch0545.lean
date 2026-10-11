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

/-! Serialized cells 545 to 554: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0545 : List ℚ := [21825/16384]
def b0546 : List ℚ := [5475/4096]
def b0547 : List ℚ := [21975/16384]
def b0548 : List ℚ := [11025/8192]
def b0549 : List ℚ := [22125/16384]
def b0550 : List ℚ := [2775/2048]
def b0551 : List ℚ := [22275/16384]
def b0552 : List ℚ := [11175/8192]
def b0553 : List ℚ := [22425/16384]
def b0554 : List ℚ := [5625/4096]

def breaks0545 : List (List ℚ) := [b0545, b0546, b0547, b0548, b0549, b0550, b0551, b0552, b0553, b0554]

theorem c0545 : checkCell pa19 (cellAt 545) b0545 = true := by decide +kernel

theorem c0546 : checkCell pa19 (cellAt 546) b0546 = true := by decide +kernel

theorem c0547 : checkCell pa19 (cellAt 547) b0547 = true := by decide +kernel

theorem c0548 : checkCell pa19 (cellAt 548) b0548 = true := by decide +kernel

theorem c0549 : checkCell pa19 (cellAt 549) b0549 = true := by decide +kernel

theorem c0550 : checkCell pa19 (cellAt 550) b0550 = true := by decide +kernel

theorem c0551 : checkCell pa19 (cellAt 551) b0551 = true := by decide +kernel

theorem c0552 : checkCell pa19 (cellAt 552) b0552 = true := by decide +kernel

theorem c0553 : checkCell pa19 (cellAt 553) b0553 = true := by decide +kernel

theorem c0554 : checkCell pa19 (cellAt 554) b0554 = true := by decide +kernel

theorem slice0545 : slice 545 10 = [cellAt 545, cellAt 546, cellAt 547, cellAt 548, cellAt 549, cellAt 550, cellAt 551, cellAt 552, cellAt 553, cellAt 554] := by decide +kernel

theorem batch0545_ok : checkAll pa19 (slice 545 10) breaks0545 = true := by
  rw [slice0545]
  simp only [breaks0545, checkAll, c0545, c0546, c0547, c0548, c0549, c0550, c0551, c0552, c0553, c0554, Bool.and_self]

theorem batch0545 : ∀ c ∈ slice 545 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0545_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0545
