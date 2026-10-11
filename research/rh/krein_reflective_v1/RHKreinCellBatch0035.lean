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

/-! Serialized cells 35 to 44: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0035 : List ℚ := [4125/32768]
def b0036 : List ℚ := [525/4096]
def b0037 : List ℚ := [4275/32768]
def b0038 : List ℚ := [2175/16384]
def b0039 : List ℚ := [4425/32768]
def b0040 : List ℚ := [1125/8192]
def b0041 : List ℚ := [4575/32768]
def b0042 : List ℚ := [2325/16384]
def b0043 : List ℚ := [4725/32768]
def b0044 : List ℚ := [75/512]

def breaks0035 : List (List ℚ) := [b0035, b0036, b0037, b0038, b0039, b0040, b0041, b0042, b0043, b0044]

theorem c0035 : checkCell pa19 (cellAt 35) b0035 = true := by decide +kernel

theorem c0036 : checkCell pa19 (cellAt 36) b0036 = true := by decide +kernel

theorem c0037 : checkCell pa19 (cellAt 37) b0037 = true := by decide +kernel

theorem c0038 : checkCell pa19 (cellAt 38) b0038 = true := by decide +kernel

theorem c0039 : checkCell pa19 (cellAt 39) b0039 = true := by decide +kernel

theorem c0040 : checkCell pa19 (cellAt 40) b0040 = true := by decide +kernel

theorem c0041 : checkCell pa19 (cellAt 41) b0041 = true := by decide +kernel

theorem c0042 : checkCell pa19 (cellAt 42) b0042 = true := by decide +kernel

theorem c0043 : checkCell pa19 (cellAt 43) b0043 = true := by decide +kernel

theorem c0044 : checkCell pa19 (cellAt 44) b0044 = true := by decide +kernel

theorem slice0035 : slice 35 10 = [cellAt 35, cellAt 36, cellAt 37, cellAt 38, cellAt 39, cellAt 40, cellAt 41, cellAt 42, cellAt 43, cellAt 44] := by decide +kernel

theorem batch0035_ok : checkAll pa19 (slice 35 10) breaks0035 = true := by
  rw [slice0035]
  simp only [breaks0035, checkAll, c0035, c0036, c0037, c0038, c0039, c0040, c0041, c0042, c0043, c0044, Bool.and_self]

theorem batch0035 : ∀ c ∈ slice 35 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0035_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0035
