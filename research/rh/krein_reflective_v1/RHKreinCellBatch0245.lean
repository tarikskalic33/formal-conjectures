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

/-! Serialized cells 245 to 254: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0245 : List ℚ := [19875/32768]
def b0246 : List ℚ := [9975/16384]
def b0247 : List ℚ := [20025/32768]
def b0248 : List ℚ := [5025/8192]
def b0249 : List ℚ := [20175/32768]
def b0250 : List ℚ := [10125/16384]
def b0251 : List ℚ := [20325/32768]
def b0252 : List ℚ := [1275/2048]
def b0253 : List ℚ := [20475/32768]
def b0254 : List ℚ := [10275/16384]

def breaks0245 : List (List ℚ) := [b0245, b0246, b0247, b0248, b0249, b0250, b0251, b0252, b0253, b0254]

theorem c0245 : checkCell pa19 (cellAt 245) b0245 = true := by decide +kernel

theorem c0246 : checkCell pa19 (cellAt 246) b0246 = true := by decide +kernel

theorem c0247 : checkCell pa19 (cellAt 247) b0247 = true := by decide +kernel

theorem c0248 : checkCell pa19 (cellAt 248) b0248 = true := by decide +kernel

theorem c0249 : checkCell pa19 (cellAt 249) b0249 = true := by decide +kernel

theorem c0250 : checkCell pa19 (cellAt 250) b0250 = true := by decide +kernel

theorem c0251 : checkCell pa19 (cellAt 251) b0251 = true := by decide +kernel

theorem c0252 : checkCell pa19 (cellAt 252) b0252 = true := by decide +kernel

theorem c0253 : checkCell pa19 (cellAt 253) b0253 = true := by decide +kernel

theorem c0254 : checkCell pa19 (cellAt 254) b0254 = true := by decide +kernel

theorem slice0245 : slice 245 10 = [cellAt 245, cellAt 246, cellAt 247, cellAt 248, cellAt 249, cellAt 250, cellAt 251, cellAt 252, cellAt 253, cellAt 254] := by decide +kernel

theorem batch0245_ok : checkAll pa19 (slice 245 10) breaks0245 = true := by
  rw [slice0245]
  simp only [breaks0245, checkAll, c0245, c0246, c0247, c0248, c0249, c0250, c0251, c0252, c0253, c0254, Bool.and_self]

theorem batch0245 : ∀ c ∈ slice 245 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0245_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0245
