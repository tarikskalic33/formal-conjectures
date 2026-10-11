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

/-! Serialized cells 125 to 134: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0125 : List ℚ := [10875/32768]
def b0126 : List ℚ := [5475/16384]
def b0127 : List ℚ := [11025/32768]
def b0128 : List ℚ := [2775/8192]
def b0129 : List ℚ := [11175/32768]
def b0130 : List ℚ := [5625/16384]
def b0131 : List ℚ := [11325/32768]
def b0132 : List ℚ := [1425/4096]
def b0133 : List ℚ := [11475/32768]
def b0134 : List ℚ := [5775/16384]

def breaks0125 : List (List ℚ) := [b0125, b0126, b0127, b0128, b0129, b0130, b0131, b0132, b0133, b0134]

theorem c0125 : checkCell pa19 (cellAt 125) b0125 = true := by decide +kernel

theorem c0126 : checkCell pa19 (cellAt 126) b0126 = true := by decide +kernel

theorem c0127 : checkCell pa19 (cellAt 127) b0127 = true := by decide +kernel

theorem c0128 : checkCell pa19 (cellAt 128) b0128 = true := by decide +kernel

theorem c0129 : checkCell pa19 (cellAt 129) b0129 = true := by decide +kernel

theorem c0130 : checkCell pa19 (cellAt 130) b0130 = true := by decide +kernel

theorem c0131 : checkCell pa19 (cellAt 131) b0131 = true := by decide +kernel

theorem c0132 : checkCell pa19 (cellAt 132) b0132 = true := by decide +kernel

theorem c0133 : checkCell pa19 (cellAt 133) b0133 = true := by decide +kernel

theorem c0134 : checkCell pa19 (cellAt 134) b0134 = true := by decide +kernel

theorem slice0125 : slice 125 10 = [cellAt 125, cellAt 126, cellAt 127, cellAt 128, cellAt 129, cellAt 130, cellAt 131, cellAt 132, cellAt 133, cellAt 134] := by decide +kernel

theorem batch0125_ok : checkAll pa19 (slice 125 10) breaks0125 = true := by
  rw [slice0125]
  simp only [breaks0125, checkAll, c0125, c0126, c0127, c0128, c0129, c0130, c0131, c0132, c0133, c0134, Bool.and_self]

theorem batch0125 : ∀ c ∈ slice 125 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0125_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0125
