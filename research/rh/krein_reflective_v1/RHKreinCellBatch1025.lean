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

/-! Serialized cells 1025 to 1034: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1025 : List ℚ := [23475/2048]
def b1026 : List ℚ := [47025/4096]
def b1027 : List ℚ := [11775/1024]
def b1028 : List ℚ := [47175/4096]
def b1029 : List ℚ := [23625/2048]
def b1030 : List ℚ := [47325/4096]
def b1031 : List ℚ := [5925/512]
def b1032 : List ℚ := [47475/4096]
def b1033 : List ℚ := [23775/2048]
def b1034 : List ℚ := [47625/4096]

def breaks1025 : List (List ℚ) := [b1025, b1026, b1027, b1028, b1029, b1030, b1031, b1032, b1033, b1034]

theorem c1025 : checkCell pa19 (cellAt 1025) b1025 = true := by decide +kernel

theorem c1026 : checkCell pa19 (cellAt 1026) b1026 = true := by decide +kernel

theorem c1027 : checkCell pa19 (cellAt 1027) b1027 = true := by decide +kernel

theorem c1028 : checkCell pa19 (cellAt 1028) b1028 = true := by decide +kernel

theorem c1029 : checkCell pa19 (cellAt 1029) b1029 = true := by decide +kernel

theorem c1030 : checkCell pa19 (cellAt 1030) b1030 = true := by decide +kernel

theorem c1031 : checkCell pa19 (cellAt 1031) b1031 = true := by decide +kernel

theorem c1032 : checkCell pa19 (cellAt 1032) b1032 = true := by decide +kernel

theorem c1033 : checkCell pa19 (cellAt 1033) b1033 = true := by decide +kernel

theorem c1034 : checkCell pa19 (cellAt 1034) b1034 = true := by decide +kernel

theorem slice1025 : slice 1025 10 = [cellAt 1025, cellAt 1026, cellAt 1027, cellAt 1028, cellAt 1029, cellAt 1030, cellAt 1031, cellAt 1032, cellAt 1033, cellAt 1034] := by decide +kernel

theorem batch1025_ok : checkAll pa19 (slice 1025 10) breaks1025 = true := by
  rw [slice1025]
  simp only [breaks1025, checkAll, c1025, c1026, c1027, c1028, c1029, c1030, c1031, c1032, c1033, c1034, Bool.and_self]

theorem batch1025 : ∀ c ∈ slice 1025 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1025_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1025
