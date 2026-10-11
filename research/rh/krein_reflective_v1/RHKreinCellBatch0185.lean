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

/-! Serialized cells 185 to 194: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0185 : List ℚ := [15375/32768]
def b0186 : List ℚ := [7725/16384]
def b0187 : List ℚ := [15525/32768]
def b0188 : List ℚ := [975/2048]
def b0189 : List ℚ := [15675/32768]
def b0190 : List ℚ := [7875/16384]
def b0191 : List ℚ := [15825/32768]
def b0192 : List ℚ := [3975/8192]
def b0193 : List ℚ := [15975/32768]
def b0194 : List ℚ := [8025/16384]

def breaks0185 : List (List ℚ) := [b0185, b0186, b0187, b0188, b0189, b0190, b0191, b0192, b0193, b0194]

theorem c0185 : checkCell pa19 (cellAt 185) b0185 = true := by decide +kernel

theorem c0186 : checkCell pa19 (cellAt 186) b0186 = true := by decide +kernel

theorem c0187 : checkCell pa19 (cellAt 187) b0187 = true := by decide +kernel

theorem c0188 : checkCell pa19 (cellAt 188) b0188 = true := by decide +kernel

theorem c0189 : checkCell pa19 (cellAt 189) b0189 = true := by decide +kernel

theorem c0190 : checkCell pa19 (cellAt 190) b0190 = true := by decide +kernel

theorem c0191 : checkCell pa19 (cellAt 191) b0191 = true := by decide +kernel

theorem c0192 : checkCell pa19 (cellAt 192) b0192 = true := by decide +kernel

theorem c0193 : checkCell pa19 (cellAt 193) b0193 = true := by decide +kernel

theorem c0194 : checkCell pa19 (cellAt 194) b0194 = true := by decide +kernel

theorem slice0185 : slice 185 10 = [cellAt 185, cellAt 186, cellAt 187, cellAt 188, cellAt 189, cellAt 190, cellAt 191, cellAt 192, cellAt 193, cellAt 194] := by decide +kernel

theorem batch0185_ok : checkAll pa19 (slice 185 10) breaks0185 = true := by
  rw [slice0185]
  simp only [breaks0185, checkAll, c0185, c0186, c0187, c0188, c0189, c0190, c0191, c0192, c0193, c0194, Bool.and_self]

theorem batch0185 : ∀ c ∈ slice 185 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0185_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0185
