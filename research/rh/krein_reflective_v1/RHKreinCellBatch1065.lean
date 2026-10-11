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

/-! Serialized cells 1065 to 1074: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1065 : List ℚ := [24975/2048]
def b1066 : List ℚ := [50025/4096]
def b1067 : List ℚ := [12525/1024]
def b1068 : List ℚ := [50175/4096]
def b1069 : List ℚ := [25125/2048]
def b1070 : List ℚ := [50325/4096]
def b1071 : List ℚ := [1575/128]
def b1072 : List ℚ := [25275/2048]
def b1073 : List ℚ := [12675/1024]
def b1074 : List ℚ := [25425/2048]

def breaks1065 : List (List ℚ) := [b1065, b1066, b1067, b1068, b1069, b1070, b1071, b1072, b1073, b1074]

theorem c1065 : checkCell pa19 (cellAt 1065) b1065 = true := by decide +kernel

theorem c1066 : checkCell pa19 (cellAt 1066) b1066 = true := by decide +kernel

theorem c1067 : checkCell pa19 (cellAt 1067) b1067 = true := by decide +kernel

theorem c1068 : checkCell pa19 (cellAt 1068) b1068 = true := by decide +kernel

theorem c1069 : checkCell pa19 (cellAt 1069) b1069 = true := by decide +kernel

theorem c1070 : checkCell pa19 (cellAt 1070) b1070 = true := by decide +kernel

theorem c1071 : checkCell pa19 (cellAt 1071) b1071 = true := by decide +kernel

theorem c1072 : checkCell pa19 (cellAt 1072) b1072 = true := by decide +kernel

theorem c1073 : checkCell pa19 (cellAt 1073) b1073 = true := by decide +kernel

theorem c1074 : checkCell pa19 (cellAt 1074) b1074 = true := by decide +kernel

theorem slice1065 : slice 1065 10 = [cellAt 1065, cellAt 1066, cellAt 1067, cellAt 1068, cellAt 1069, cellAt 1070, cellAt 1071, cellAt 1072, cellAt 1073, cellAt 1074] := by decide +kernel

theorem batch1065_ok : checkAll pa19 (slice 1065 10) breaks1065 = true := by
  rw [slice1065]
  simp only [breaks1065, checkAll, c1065, c1066, c1067, c1068, c1069, c1070, c1071, c1072, c1073, c1074, Bool.and_self]

theorem batch1065 : ∀ c ∈ slice 1065 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1065_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1065
