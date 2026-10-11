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

/-! Serialized cells 85 to 94: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0085 : List ℚ := [7875/32768]
def b0086 : List ℚ := [3975/16384]
def b0087 : List ℚ := [8025/32768]
def b0088 : List ℚ := [2025/8192]
def b0089 : List ℚ := [8175/32768]
def b0090 : List ℚ := [4125/16384]
def b0091 : List ℚ := [8325/32768]
def b0092 : List ℚ := [525/2048]
def b0093 : List ℚ := [8475/32768]
def b0094 : List ℚ := [4275/16384]

def breaks0085 : List (List ℚ) := [b0085, b0086, b0087, b0088, b0089, b0090, b0091, b0092, b0093, b0094]

theorem c0085 : checkCell pa19 (cellAt 85) b0085 = true := by decide +kernel

theorem c0086 : checkCell pa19 (cellAt 86) b0086 = true := by decide +kernel

theorem c0087 : checkCell pa19 (cellAt 87) b0087 = true := by decide +kernel

theorem c0088 : checkCell pa19 (cellAt 88) b0088 = true := by decide +kernel

theorem c0089 : checkCell pa19 (cellAt 89) b0089 = true := by decide +kernel

theorem c0090 : checkCell pa19 (cellAt 90) b0090 = true := by decide +kernel

theorem c0091 : checkCell pa19 (cellAt 91) b0091 = true := by decide +kernel

theorem c0092 : checkCell pa19 (cellAt 92) b0092 = true := by decide +kernel

theorem c0093 : checkCell pa19 (cellAt 93) b0093 = true := by decide +kernel

theorem c0094 : checkCell pa19 (cellAt 94) b0094 = true := by decide +kernel

theorem slice0085 : slice 85 10 = [cellAt 85, cellAt 86, cellAt 87, cellAt 88, cellAt 89, cellAt 90, cellAt 91, cellAt 92, cellAt 93, cellAt 94] := by decide +kernel

theorem batch0085_ok : checkAll pa19 (slice 85 10) breaks0085 = true := by
  rw [slice0085]
  simp only [breaks0085, checkAll, c0085, c0086, c0087, c0088, c0089, c0090, c0091, c0092, c0093, c0094, Bool.and_self]

theorem batch0085 : ∀ c ∈ slice 85 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0085_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0085
