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

/-! Serialized cells 135 to 144: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0135 : List ℚ := [11625/32768]
def b0136 : List ℚ := [2925/8192]
def b0137 : List ℚ := [11775/32768]
def b0138 : List ℚ := [5925/16384]
def b0139 : List ℚ := [11925/32768]
def b0140 : List ℚ := [375/1024]
def b0141 : List ℚ := [12075/32768]
def b0142 : List ℚ := [6075/16384]
def b0143 : List ℚ := [12225/32768]
def b0144 : List ℚ := [3075/8192]

def breaks0135 : List (List ℚ) := [b0135, b0136, b0137, b0138, b0139, b0140, b0141, b0142, b0143, b0144]

theorem c0135 : checkCell pa19 (cellAt 135) b0135 = true := by decide +kernel

theorem c0136 : checkCell pa19 (cellAt 136) b0136 = true := by decide +kernel

theorem c0137 : checkCell pa19 (cellAt 137) b0137 = true := by decide +kernel

theorem c0138 : checkCell pa19 (cellAt 138) b0138 = true := by decide +kernel

theorem c0139 : checkCell pa19 (cellAt 139) b0139 = true := by decide +kernel

theorem c0140 : checkCell pa19 (cellAt 140) b0140 = true := by decide +kernel

theorem c0141 : checkCell pa19 (cellAt 141) b0141 = true := by decide +kernel

theorem c0142 : checkCell pa19 (cellAt 142) b0142 = true := by decide +kernel

theorem c0143 : checkCell pa19 (cellAt 143) b0143 = true := by decide +kernel

theorem c0144 : checkCell pa19 (cellAt 144) b0144 = true := by decide +kernel

theorem slice0135 : slice 135 10 = [cellAt 135, cellAt 136, cellAt 137, cellAt 138, cellAt 139, cellAt 140, cellAt 141, cellAt 142, cellAt 143, cellAt 144] := by decide +kernel

theorem batch0135_ok : checkAll pa19 (slice 135 10) breaks0135 = true := by
  rw [slice0135]
  simp only [breaks0135, checkAll, c0135, c0136, c0137, c0138, c0139, c0140, c0141, c0142, c0143, c0144, Bool.and_self]

theorem batch0135 : ∀ c ∈ slice 135 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0135_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0135
