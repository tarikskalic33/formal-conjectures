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

/-! Serialized cells 265 to 274: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0265 : List ℚ := [21375/32768]
def b0266 : List ℚ := [10725/16384]
def b0267 : List ℚ := [21525/32768]
def b0268 : List ℚ := [675/1024]
def b0269 : List ℚ := [21675/32768]
def b0270 : List ℚ := [10875/16384]
def b0271 : List ℚ := [21825/32768]
def b0272 : List ℚ := [5475/8192]
def b0273 : List ℚ := [21975/32768]
def b0274 : List ℚ := [11025/16384]

def breaks0265 : List (List ℚ) := [b0265, b0266, b0267, b0268, b0269, b0270, b0271, b0272, b0273, b0274]

theorem c0265 : checkCell pa19 (cellAt 265) b0265 = true := by decide +kernel

theorem c0266 : checkCell pa19 (cellAt 266) b0266 = true := by decide +kernel

theorem c0267 : checkCell pa19 (cellAt 267) b0267 = true := by decide +kernel

theorem c0268 : checkCell pa19 (cellAt 268) b0268 = true := by decide +kernel

theorem c0269 : checkCell pa19 (cellAt 269) b0269 = true := by decide +kernel

theorem c0270 : checkCell pa19 (cellAt 270) b0270 = true := by decide +kernel

theorem c0271 : checkCell pa19 (cellAt 271) b0271 = true := by decide +kernel

theorem c0272 : checkCell pa19 (cellAt 272) b0272 = true := by decide +kernel

theorem c0273 : checkCell pa19 (cellAt 273) b0273 = true := by decide +kernel

theorem c0274 : checkCell pa19 (cellAt 274) b0274 = true := by decide +kernel

theorem slice0265 : slice 265 10 = [cellAt 265, cellAt 266, cellAt 267, cellAt 268, cellAt 269, cellAt 270, cellAt 271, cellAt 272, cellAt 273, cellAt 274] := by decide +kernel

theorem batch0265_ok : checkAll pa19 (slice 265 10) breaks0265 = true := by
  rw [slice0265]
  simp only [breaks0265, checkAll, c0265, c0266, c0267, c0268, c0269, c0270, c0271, c0272, c0273, c0274, Bool.and_self]

theorem batch0265 : ∀ c ∈ slice 265 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0265_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0265
