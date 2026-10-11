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

/-! Serialized cells 565 to 574: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0565 : List ℚ := [23325/16384]
def b0566 : List ℚ := [2925/2048]
def b0567 : List ℚ := [23475/16384]
def b0568 : List ℚ := [11775/8192]
def b0569 : List ℚ := [23625/16384]
def b0570 : List ℚ := [5925/4096]
def b0571 : List ℚ := [23775/16384]
def b0572 : List ℚ := [11925/8192]
def b0573 : List ℚ := [23925/16384]
def b0574 : List ℚ := [375/256]

def breaks0565 : List (List ℚ) := [b0565, b0566, b0567, b0568, b0569, b0570, b0571, b0572, b0573, b0574]

theorem c0565 : checkCell pa19 (cellAt 565) b0565 = true := by decide +kernel

theorem c0566 : checkCell pa19 (cellAt 566) b0566 = true := by decide +kernel

theorem c0567 : checkCell pa19 (cellAt 567) b0567 = true := by decide +kernel

theorem c0568 : checkCell pa19 (cellAt 568) b0568 = true := by decide +kernel

theorem c0569 : checkCell pa19 (cellAt 569) b0569 = true := by decide +kernel

theorem c0570 : checkCell pa19 (cellAt 570) b0570 = true := by decide +kernel

theorem c0571 : checkCell pa19 (cellAt 571) b0571 = true := by decide +kernel

theorem c0572 : checkCell pa19 (cellAt 572) b0572 = true := by decide +kernel

theorem c0573 : checkCell pa19 (cellAt 573) b0573 = true := by decide +kernel

theorem c0574 : checkCell pa19 (cellAt 574) b0574 = true := by decide +kernel

theorem slice0565 : slice 565 10 = [cellAt 565, cellAt 566, cellAt 567, cellAt 568, cellAt 569, cellAt 570, cellAt 571, cellAt 572, cellAt 573, cellAt 574] := by decide +kernel

theorem batch0565_ok : checkAll pa19 (slice 565 10) breaks0565 = true := by
  rw [slice0565]
  simp only [breaks0565, checkAll, c0565, c0566, c0567, c0568, c0569, c0570, c0571, c0572, c0573, c0574, Bool.and_self]

theorem batch0565 : ∀ c ∈ slice 565 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0565_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0565
