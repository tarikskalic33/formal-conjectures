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

/-! Serialized cells 285 to 294: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0285 : List ℚ := [22875/32768]
def b0286 : List ℚ := [11475/16384]
def b0287 : List ℚ := [23025/32768]
def b0288 : List ℚ := [5775/8192]
def b0289 : List ℚ := [23175/32768]
def b0290 : List ℚ := [11625/16384]
def b0291 : List ℚ := [23325/32768]
def b0292 : List ℚ := [2925/4096]
def b0293 : List ℚ := [23475/32768]
def b0294 : List ℚ := [11775/16384]

def breaks0285 : List (List ℚ) := [b0285, b0286, b0287, b0288, b0289, b0290, b0291, b0292, b0293, b0294]

theorem c0285 : checkCell pa19 (cellAt 285) b0285 = true := by decide +kernel

theorem c0286 : checkCell pa19 (cellAt 286) b0286 = true := by decide +kernel

theorem c0287 : checkCell pa19 (cellAt 287) b0287 = true := by decide +kernel

theorem c0288 : checkCell pa19 (cellAt 288) b0288 = true := by decide +kernel

theorem c0289 : checkCell pa19 (cellAt 289) b0289 = true := by decide +kernel

theorem c0290 : checkCell pa19 (cellAt 290) b0290 = true := by decide +kernel

theorem c0291 : checkCell pa19 (cellAt 291) b0291 = true := by decide +kernel

theorem c0292 : checkCell pa19 (cellAt 292) b0292 = true := by decide +kernel

theorem c0293 : checkCell pa19 (cellAt 293) b0293 = true := by decide +kernel

theorem c0294 : checkCell pa19 (cellAt 294) b0294 = true := by decide +kernel

theorem slice0285 : slice 285 10 = [cellAt 285, cellAt 286, cellAt 287, cellAt 288, cellAt 289, cellAt 290, cellAt 291, cellAt 292, cellAt 293, cellAt 294] := by decide +kernel

theorem batch0285_ok : checkAll pa19 (slice 285 10) breaks0285 = true := by
  rw [slice0285]
  simp only [breaks0285, checkAll, c0285, c0286, c0287, c0288, c0289, c0290, c0291, c0292, c0293, c0294, Bool.and_self]

theorem batch0285 : ∀ c ∈ slice 285 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0285_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0285
