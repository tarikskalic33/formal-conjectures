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

/-! Serialized cells 115 to 124: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0115 : List ℚ := [10125/32768]
def b0116 : List ℚ := [1275/4096]
def b0117 : List ℚ := [10275/32768]
def b0118 : List ℚ := [5175/16384]
def b0119 : List ℚ := [10425/32768]
def b0120 : List ℚ := [2625/8192]
def b0121 : List ℚ := [10575/32768]
def b0122 : List ℚ := [5325/16384]
def b0123 : List ℚ := [10725/32768]
def b0124 : List ℚ := [675/2048]

def breaks0115 : List (List ℚ) := [b0115, b0116, b0117, b0118, b0119, b0120, b0121, b0122, b0123, b0124]

theorem c0115 : checkCell pa19 (cellAt 115) b0115 = true := by decide +kernel

theorem c0116 : checkCell pa19 (cellAt 116) b0116 = true := by decide +kernel

theorem c0117 : checkCell pa19 (cellAt 117) b0117 = true := by decide +kernel

theorem c0118 : checkCell pa19 (cellAt 118) b0118 = true := by decide +kernel

theorem c0119 : checkCell pa19 (cellAt 119) b0119 = true := by decide +kernel

theorem c0120 : checkCell pa19 (cellAt 120) b0120 = true := by decide +kernel

theorem c0121 : checkCell pa19 (cellAt 121) b0121 = true := by decide +kernel

theorem c0122 : checkCell pa19 (cellAt 122) b0122 = true := by decide +kernel

theorem c0123 : checkCell pa19 (cellAt 123) b0123 = true := by decide +kernel

theorem c0124 : checkCell pa19 (cellAt 124) b0124 = true := by decide +kernel

theorem slice0115 : slice 115 10 = [cellAt 115, cellAt 116, cellAt 117, cellAt 118, cellAt 119, cellAt 120, cellAt 121, cellAt 122, cellAt 123, cellAt 124] := by decide +kernel

theorem batch0115_ok : checkAll pa19 (slice 115 10) breaks0115 = true := by
  rw [slice0115]
  simp only [breaks0115, checkAll, c0115, c0116, c0117, c0118, c0119, c0120, c0121, c0122, c0123, c0124, Bool.and_self]

theorem batch0115 : ∀ c ∈ slice 115 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0115_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0115
