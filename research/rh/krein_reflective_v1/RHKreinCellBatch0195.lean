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

/-! Serialized cells 195 to 204: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0195 : List ℚ := [16125/32768]
def b0196 : List ℚ := [2025/4096]
def b0197 : List ℚ := [16275/32768]
def b0198 : List ℚ := [8175/16384]
def b0199 : List ℚ := [16425/32768]
def b0200 : List ℚ := [4125/8192]
def b0201 : List ℚ := [16575/32768]
def b0202 : List ℚ := [8325/16384]
def b0203 : List ℚ := [16725/32768]
def b0204 : List ℚ := [525/1024]

def breaks0195 : List (List ℚ) := [b0195, b0196, b0197, b0198, b0199, b0200, b0201, b0202, b0203, b0204]

theorem c0195 : checkCell pa19 (cellAt 195) b0195 = true := by decide +kernel

theorem c0196 : checkCell pa19 (cellAt 196) b0196 = true := by decide +kernel

theorem c0197 : checkCell pa19 (cellAt 197) b0197 = true := by decide +kernel

theorem c0198 : checkCell pa19 (cellAt 198) b0198 = true := by decide +kernel

theorem c0199 : checkCell pa19 (cellAt 199) b0199 = true := by decide +kernel

theorem c0200 : checkCell pa19 (cellAt 200) b0200 = true := by decide +kernel

theorem c0201 : checkCell pa19 (cellAt 201) b0201 = true := by decide +kernel

theorem c0202 : checkCell pa19 (cellAt 202) b0202 = true := by decide +kernel

theorem c0203 : checkCell pa19 (cellAt 203) b0203 = true := by decide +kernel

theorem c0204 : checkCell pa19 (cellAt 204) b0204 = true := by decide +kernel

theorem slice0195 : slice 195 10 = [cellAt 195, cellAt 196, cellAt 197, cellAt 198, cellAt 199, cellAt 200, cellAt 201, cellAt 202, cellAt 203, cellAt 204] := by decide +kernel

theorem batch0195_ok : checkAll pa19 (slice 195 10) breaks0195 = true := by
  rw [slice0195]
  simp only [breaks0195, checkAll, c0195, c0196, c0197, c0198, c0199, c0200, c0201, c0202, c0203, c0204, Bool.and_self]

theorem batch0195 : ∀ c ∈ slice 195 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0195_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0195
