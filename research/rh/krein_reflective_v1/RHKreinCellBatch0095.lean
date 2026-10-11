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

/-! Serialized cells 95 to 104: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0095 : List ℚ := [8625/32768]
def b0096 : List ℚ := [2175/8192]
def b0097 : List ℚ := [8775/32768]
def b0098 : List ℚ := [4425/16384]
def b0099 : List ℚ := [8925/32768]
def b0100 : List ℚ := [1125/4096]
def b0101 : List ℚ := [9075/32768]
def b0102 : List ℚ := [4575/16384]
def b0103 : List ℚ := [9225/32768]
def b0104 : List ℚ := [2325/8192]

def breaks0095 : List (List ℚ) := [b0095, b0096, b0097, b0098, b0099, b0100, b0101, b0102, b0103, b0104]

theorem c0095 : checkCell pa19 (cellAt 95) b0095 = true := by decide +kernel

theorem c0096 : checkCell pa19 (cellAt 96) b0096 = true := by decide +kernel

theorem c0097 : checkCell pa19 (cellAt 97) b0097 = true := by decide +kernel

theorem c0098 : checkCell pa19 (cellAt 98) b0098 = true := by decide +kernel

theorem c0099 : checkCell pa19 (cellAt 99) b0099 = true := by decide +kernel

theorem c0100 : checkCell pa19 (cellAt 100) b0100 = true := by decide +kernel

theorem c0101 : checkCell pa19 (cellAt 101) b0101 = true := by decide +kernel

theorem c0102 : checkCell pa19 (cellAt 102) b0102 = true := by decide +kernel

theorem c0103 : checkCell pa19 (cellAt 103) b0103 = true := by decide +kernel

theorem c0104 : checkCell pa19 (cellAt 104) b0104 = true := by decide +kernel

theorem slice0095 : slice 95 10 = [cellAt 95, cellAt 96, cellAt 97, cellAt 98, cellAt 99, cellAt 100, cellAt 101, cellAt 102, cellAt 103, cellAt 104] := by decide +kernel

theorem batch0095_ok : checkAll pa19 (slice 95 10) breaks0095 = true := by
  rw [slice0095]
  simp only [breaks0095, checkAll, c0095, c0096, c0097, c0098, c0099, c0100, c0101, c0102, c0103, c0104, Bool.and_self]

theorem batch0095 : ∀ c ∈ slice 95 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0095_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0095
