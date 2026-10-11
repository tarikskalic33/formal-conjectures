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

/-! Serialized cells 225 to 234: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0225 : List ℚ := [18375/32768]
def b0226 : List ℚ := [9225/16384]
def b0227 : List ℚ := [18525/32768]
def b0228 : List ℚ := [2325/4096]
def b0229 : List ℚ := [18675/32768]
def b0230 : List ℚ := [9375/16384]
def b0231 : List ℚ := [18825/32768]
def b0232 : List ℚ := [4725/8192]
def b0233 : List ℚ := [18975/32768]
def b0234 : List ℚ := [9525/16384]

def breaks0225 : List (List ℚ) := [b0225, b0226, b0227, b0228, b0229, b0230, b0231, b0232, b0233, b0234]

theorem c0225 : checkCell pa19 (cellAt 225) b0225 = true := by decide +kernel

theorem c0226 : checkCell pa19 (cellAt 226) b0226 = true := by decide +kernel

theorem c0227 : checkCell pa19 (cellAt 227) b0227 = true := by decide +kernel

theorem c0228 : checkCell pa19 (cellAt 228) b0228 = true := by decide +kernel

theorem c0229 : checkCell pa19 (cellAt 229) b0229 = true := by decide +kernel

theorem c0230 : checkCell pa19 (cellAt 230) b0230 = true := by decide +kernel

theorem c0231 : checkCell pa19 (cellAt 231) b0231 = true := by decide +kernel

theorem c0232 : checkCell pa19 (cellAt 232) b0232 = true := by decide +kernel

theorem c0233 : checkCell pa19 (cellAt 233) b0233 = true := by decide +kernel

theorem c0234 : checkCell pa19 (cellAt 234) b0234 = true := by decide +kernel

theorem slice0225 : slice 225 10 = [cellAt 225, cellAt 226, cellAt 227, cellAt 228, cellAt 229, cellAt 230, cellAt 231, cellAt 232, cellAt 233, cellAt 234] := by decide +kernel

theorem batch0225_ok : checkAll pa19 (slice 225 10) breaks0225 = true := by
  rw [slice0225]
  simp only [breaks0225, checkAll, c0225, c0226, c0227, c0228, c0229, c0230, c0231, c0232, c0233, c0234, Bool.and_self]

theorem batch0225 : ∀ c ∈ slice 225 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0225_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0225
