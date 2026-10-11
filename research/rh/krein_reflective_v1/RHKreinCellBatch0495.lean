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

/-! Serialized cells 495 to 504: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0495 : List ℚ := [38625/32768]
def b0496 : List ℚ := [9675/8192]
def b0497 : List ℚ := [38775/32768]
def b0498 : List ℚ := [19425/16384]
def b0499 : List ℚ := [38925/32768]
def b0500 : List ℚ := [4875/4096]
def b0501 : List ℚ := [39075/32768]
def b0502 : List ℚ := [19575/16384]
def b0503 : List ℚ := [39225/32768]
def b0504 : List ℚ := [9825/8192]

def breaks0495 : List (List ℚ) := [b0495, b0496, b0497, b0498, b0499, b0500, b0501, b0502, b0503, b0504]

theorem c0495 : checkCell pa19 (cellAt 495) b0495 = true := by decide +kernel

theorem c0496 : checkCell pa19 (cellAt 496) b0496 = true := by decide +kernel

theorem c0497 : checkCell pa19 (cellAt 497) b0497 = true := by decide +kernel

theorem c0498 : checkCell pa19 (cellAt 498) b0498 = true := by decide +kernel

theorem c0499 : checkCell pa19 (cellAt 499) b0499 = true := by decide +kernel

theorem c0500 : checkCell pa19 (cellAt 500) b0500 = true := by decide +kernel

theorem c0501 : checkCell pa19 (cellAt 501) b0501 = true := by decide +kernel

theorem c0502 : checkCell pa19 (cellAt 502) b0502 = true := by decide +kernel

theorem c0503 : checkCell pa19 (cellAt 503) b0503 = true := by decide +kernel

theorem c0504 : checkCell pa19 (cellAt 504) b0504 = true := by decide +kernel

theorem slice0495 : slice 495 10 = [cellAt 495, cellAt 496, cellAt 497, cellAt 498, cellAt 499, cellAt 500, cellAt 501, cellAt 502, cellAt 503, cellAt 504] := by decide +kernel

theorem batch0495_ok : checkAll pa19 (slice 495 10) breaks0495 = true := by
  rw [slice0495]
  simp only [breaks0495, checkAll, c0495, c0496, c0497, c0498, c0499, c0500, c0501, c0502, c0503, c0504, Bool.and_self]

theorem batch0495 : ∀ c ∈ slice 495 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0495_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0495
