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

/-! Serialized cells 25 to 34: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0025 : List ℚ := [3375/32768]
def b0026 : List ℚ := [1725/16384]
def b0027 : List ℚ := [3525/32768]
def b0028 : List ℚ := [225/2048]
def b0029 : List ℚ := [3675/32768]
def b0030 : List ℚ := [1875/16384]
def b0031 : List ℚ := [3825/32768]
def b0032 : List ℚ := [975/8192]
def b0033 : List ℚ := [3975/32768]
def b0034 : List ℚ := [2025/16384]

def breaks0025 : List (List ℚ) := [b0025, b0026, b0027, b0028, b0029, b0030, b0031, b0032, b0033, b0034]

theorem c0025 : checkCell pa19 (cellAt 25) b0025 = true := by decide +kernel

theorem c0026 : checkCell pa19 (cellAt 26) b0026 = true := by decide +kernel

theorem c0027 : checkCell pa19 (cellAt 27) b0027 = true := by decide +kernel

theorem c0028 : checkCell pa19 (cellAt 28) b0028 = true := by decide +kernel

theorem c0029 : checkCell pa19 (cellAt 29) b0029 = true := by decide +kernel

theorem c0030 : checkCell pa19 (cellAt 30) b0030 = true := by decide +kernel

theorem c0031 : checkCell pa19 (cellAt 31) b0031 = true := by decide +kernel

theorem c0032 : checkCell pa19 (cellAt 32) b0032 = true := by decide +kernel

theorem c0033 : checkCell pa19 (cellAt 33) b0033 = true := by decide +kernel

theorem c0034 : checkCell pa19 (cellAt 34) b0034 = true := by decide +kernel

theorem slice0025 : slice 25 10 = [cellAt 25, cellAt 26, cellAt 27, cellAt 28, cellAt 29, cellAt 30, cellAt 31, cellAt 32, cellAt 33, cellAt 34] := by decide +kernel

theorem batch0025_ok : checkAll pa19 (slice 25 10) breaks0025 = true := by
  rw [slice0025]
  simp only [breaks0025, checkAll, c0025, c0026, c0027, c0028, c0029, c0030, c0031, c0032, c0033, c0034, Bool.and_self]

theorem batch0025 : ∀ c ∈ slice 25 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0025_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0025
