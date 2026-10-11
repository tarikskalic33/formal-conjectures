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

/-! Serialized cells 75 to 84: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0075 : List ℚ := [7125/32768]
def b0076 : List ℚ := [225/1024]
def b0077 : List ℚ := [7275/32768]
def b0078 : List ℚ := [3675/16384]
def b0079 : List ℚ := [7425/32768]
def b0080 : List ℚ := [1875/8192]
def b0081 : List ℚ := [7575/32768]
def b0082 : List ℚ := [3825/16384]
def b0083 : List ℚ := [7725/32768]
def b0084 : List ℚ := [975/4096]

def breaks0075 : List (List ℚ) := [b0075, b0076, b0077, b0078, b0079, b0080, b0081, b0082, b0083, b0084]

theorem c0075 : checkCell pa19 (cellAt 75) b0075 = true := by decide +kernel

theorem c0076 : checkCell pa19 (cellAt 76) b0076 = true := by decide +kernel

theorem c0077 : checkCell pa19 (cellAt 77) b0077 = true := by decide +kernel

theorem c0078 : checkCell pa19 (cellAt 78) b0078 = true := by decide +kernel

theorem c0079 : checkCell pa19 (cellAt 79) b0079 = true := by decide +kernel

theorem c0080 : checkCell pa19 (cellAt 80) b0080 = true := by decide +kernel

theorem c0081 : checkCell pa19 (cellAt 81) b0081 = true := by decide +kernel

theorem c0082 : checkCell pa19 (cellAt 82) b0082 = true := by decide +kernel

theorem c0083 : checkCell pa19 (cellAt 83) b0083 = true := by decide +kernel

theorem c0084 : checkCell pa19 (cellAt 84) b0084 = true := by decide +kernel

theorem slice0075 : slice 75 10 = [cellAt 75, cellAt 76, cellAt 77, cellAt 78, cellAt 79, cellAt 80, cellAt 81, cellAt 82, cellAt 83, cellAt 84] := by decide +kernel

theorem batch0075_ok : checkAll pa19 (slice 75 10) breaks0075 = true := by
  rw [slice0075]
  simp only [breaks0075, checkAll, c0075, c0076, c0077, c0078, c0079, c0080, c0081, c0082, c0083, c0084, Bool.and_self]

theorem batch0075 : ∀ c ∈ slice 75 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0075_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0075
