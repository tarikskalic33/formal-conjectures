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

/-! Serialized cells 725 to 734: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0725 : List ℚ := [2625/1024]
def b0726 : List ℚ := [10575/4096]
def b0727 : List ℚ := [5325/2048]
def b0728 : List ℚ := [10725/4096]
def b0729 : List ℚ := [675/256]
def b0730 : List ℚ := [10875/4096]
def b0731 : List ℚ := [5475/2048]
def b0732 : List ℚ := [11025/4096]
def b0733 : List ℚ := [2775/1024]
def b0734 : List ℚ := [11175/4096]

def breaks0725 : List (List ℚ) := [b0725, b0726, b0727, b0728, b0729, b0730, b0731, b0732, b0733, b0734]

theorem c0725 : checkCell pa19 (cellAt 725) b0725 = true := by decide +kernel

theorem c0726 : checkCell pa19 (cellAt 726) b0726 = true := by decide +kernel

theorem c0727 : checkCell pa19 (cellAt 727) b0727 = true := by decide +kernel

theorem c0728 : checkCell pa19 (cellAt 728) b0728 = true := by decide +kernel

theorem c0729 : checkCell pa19 (cellAt 729) b0729 = true := by decide +kernel

theorem c0730 : checkCell pa19 (cellAt 730) b0730 = true := by decide +kernel

theorem c0731 : checkCell pa19 (cellAt 731) b0731 = true := by decide +kernel

theorem c0732 : checkCell pa19 (cellAt 732) b0732 = true := by decide +kernel

theorem c0733 : checkCell pa19 (cellAt 733) b0733 = true := by decide +kernel

theorem c0734 : checkCell pa19 (cellAt 734) b0734 = true := by decide +kernel

theorem slice0725 : slice 725 10 = [cellAt 725, cellAt 726, cellAt 727, cellAt 728, cellAt 729, cellAt 730, cellAt 731, cellAt 732, cellAt 733, cellAt 734] := by decide +kernel

theorem batch0725_ok : checkAll pa19 (slice 725 10) breaks0725 = true := by
  rw [slice0725]
  simp only [breaks0725, checkAll, c0725, c0726, c0727, c0728, c0729, c0730, c0731, c0732, c0733, c0734, Bool.and_self]

theorem batch0725 : ∀ c ∈ slice 725 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0725_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0725
