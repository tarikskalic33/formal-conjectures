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

/-! Serialized cells 155 to 164: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0155 : List ℚ := [13125/32768]
def b0156 : List ℚ := [825/2048]
def b0157 : List ℚ := [13275/32768]
def b0158 : List ℚ := [6675/16384]
def b0159 : List ℚ := [13425/32768]
def b0160 : List ℚ := [3375/8192]
def b0161 : List ℚ := [13575/32768]
def b0162 : List ℚ := [6825/16384]
def b0163 : List ℚ := [13725/32768]
def b0164 : List ℚ := [1725/4096]

def breaks0155 : List (List ℚ) := [b0155, b0156, b0157, b0158, b0159, b0160, b0161, b0162, b0163, b0164]

theorem c0155 : checkCell pa19 (cellAt 155) b0155 = true := by decide +kernel

theorem c0156 : checkCell pa19 (cellAt 156) b0156 = true := by decide +kernel

theorem c0157 : checkCell pa19 (cellAt 157) b0157 = true := by decide +kernel

theorem c0158 : checkCell pa19 (cellAt 158) b0158 = true := by decide +kernel

theorem c0159 : checkCell pa19 (cellAt 159) b0159 = true := by decide +kernel

theorem c0160 : checkCell pa19 (cellAt 160) b0160 = true := by decide +kernel

theorem c0161 : checkCell pa19 (cellAt 161) b0161 = true := by decide +kernel

theorem c0162 : checkCell pa19 (cellAt 162) b0162 = true := by decide +kernel

theorem c0163 : checkCell pa19 (cellAt 163) b0163 = true := by decide +kernel

theorem c0164 : checkCell pa19 (cellAt 164) b0164 = true := by decide +kernel

theorem slice0155 : slice 155 10 = [cellAt 155, cellAt 156, cellAt 157, cellAt 158, cellAt 159, cellAt 160, cellAt 161, cellAt 162, cellAt 163, cellAt 164] := by decide +kernel

theorem batch0155_ok : checkAll pa19 (slice 155 10) breaks0155 = true := by
  rw [slice0155]
  simp only [breaks0155, checkAll, c0155, c0156, c0157, c0158, c0159, c0160, c0161, c0162, c0163, c0164, Bool.and_self]

theorem batch0155 : ∀ c ∈ slice 155 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0155_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0155
