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

/-! Serialized cells 65 to 74: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0065 : List ℚ := [6375/32768]
def b0066 : List ℚ := [3225/16384]
def b0067 : List ℚ := [6525/32768]
def b0068 : List ℚ := [825/4096]
def b0069 : List ℚ := [6675/32768]
def b0070 : List ℚ := [3375/16384]
def b0071 : List ℚ := [6825/32768]
def b0072 : List ℚ := [1725/8192]
def b0073 : List ℚ := [6975/32768]
def b0074 : List ℚ := [3525/16384]

def breaks0065 : List (List ℚ) := [b0065, b0066, b0067, b0068, b0069, b0070, b0071, b0072, b0073, b0074]

theorem c0065 : checkCell pa19 (cellAt 65) b0065 = true := by decide +kernel

theorem c0066 : checkCell pa19 (cellAt 66) b0066 = true := by decide +kernel

theorem c0067 : checkCell pa19 (cellAt 67) b0067 = true := by decide +kernel

theorem c0068 : checkCell pa19 (cellAt 68) b0068 = true := by decide +kernel

theorem c0069 : checkCell pa19 (cellAt 69) b0069 = true := by decide +kernel

theorem c0070 : checkCell pa19 (cellAt 70) b0070 = true := by decide +kernel

theorem c0071 : checkCell pa19 (cellAt 71) b0071 = true := by decide +kernel

theorem c0072 : checkCell pa19 (cellAt 72) b0072 = true := by decide +kernel

theorem c0073 : checkCell pa19 (cellAt 73) b0073 = true := by decide +kernel

theorem c0074 : checkCell pa19 (cellAt 74) b0074 = true := by decide +kernel

theorem slice0065 : slice 65 10 = [cellAt 65, cellAt 66, cellAt 67, cellAt 68, cellAt 69, cellAt 70, cellAt 71, cellAt 72, cellAt 73, cellAt 74] := by decide +kernel

theorem batch0065_ok : checkAll pa19 (slice 65 10) breaks0065 = true := by
  rw [slice0065]
  simp only [breaks0065, checkAll, c0065, c0066, c0067, c0068, c0069, c0070, c0071, c0072, c0073, c0074, Bool.and_self]

theorem batch0065 : ∀ c ∈ slice 65 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0065_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0065
