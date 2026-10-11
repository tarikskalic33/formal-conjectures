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

/-! Serialized cells 305 to 314: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0305 : List ℚ := [24375/32768]
def b0306 : List ℚ := [12225/16384]
def b0307 : List ℚ := [24525/32768]
def b0308 : List ℚ := [3075/4096]
def b0309 : List ℚ := [24675/32768]
def b0310 : List ℚ := [12375/16384]
def b0311 : List ℚ := [24825/32768]
def b0312 : List ℚ := [6225/8192]
def b0313 : List ℚ := [24975/32768]
def b0314 : List ℚ := [12525/16384]

def breaks0305 : List (List ℚ) := [b0305, b0306, b0307, b0308, b0309, b0310, b0311, b0312, b0313, b0314]

theorem c0305 : checkCell pa19 (cellAt 305) b0305 = true := by decide +kernel

theorem c0306 : checkCell pa19 (cellAt 306) b0306 = true := by decide +kernel

theorem c0307 : checkCell pa19 (cellAt 307) b0307 = true := by decide +kernel

theorem c0308 : checkCell pa19 (cellAt 308) b0308 = true := by decide +kernel

theorem c0309 : checkCell pa19 (cellAt 309) b0309 = true := by decide +kernel

theorem c0310 : checkCell pa19 (cellAt 310) b0310 = true := by decide +kernel

theorem c0311 : checkCell pa19 (cellAt 311) b0311 = true := by decide +kernel

theorem c0312 : checkCell pa19 (cellAt 312) b0312 = true := by decide +kernel

theorem c0313 : checkCell pa19 (cellAt 313) b0313 = true := by decide +kernel

theorem c0314 : checkCell pa19 (cellAt 314) b0314 = true := by decide +kernel

theorem slice0305 : slice 305 10 = [cellAt 305, cellAt 306, cellAt 307, cellAt 308, cellAt 309, cellAt 310, cellAt 311, cellAt 312, cellAt 313, cellAt 314] := by decide +kernel

theorem batch0305_ok : checkAll pa19 (slice 305 10) breaks0305 = true := by
  rw [slice0305]
  simp only [breaks0305, checkAll, c0305, c0306, c0307, c0308, c0309, c0310, c0311, c0312, c0313, c0314, Bool.and_self]

theorem batch0305 : ∀ c ∈ slice 305 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0305_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0305
