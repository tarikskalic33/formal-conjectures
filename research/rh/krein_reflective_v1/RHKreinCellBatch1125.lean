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

/-! Serialized cells 1125 to 1134: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1125 : List ℚ := [4275/256]
def b1126 : List ℚ := [17175/1024]
def b1127 : List ℚ := [8625/512]
def b1128 : List ℚ := [17325/1024]
def b1129 : List ℚ := [2175/128]
def b1130 : List ℚ := [17475/1024]
def b1131 : List ℚ := [8775/512]
def b1132 : List ℚ := [17625/1024]
def b1133 : List ℚ := [4425/256]
def b1134 : List ℚ := [17775/1024]

def breaks1125 : List (List ℚ) := [b1125, b1126, b1127, b1128, b1129, b1130, b1131, b1132, b1133, b1134]

theorem c1125 : checkCell pa19 (cellAt 1125) b1125 = true := by decide +kernel

theorem c1126 : checkCell pa19 (cellAt 1126) b1126 = true := by decide +kernel

theorem c1127 : checkCell pa19 (cellAt 1127) b1127 = true := by decide +kernel

theorem c1128 : checkCell pa19 (cellAt 1128) b1128 = true := by decide +kernel

theorem c1129 : checkCell pa19 (cellAt 1129) b1129 = true := by decide +kernel

theorem c1130 : checkCell pa19 (cellAt 1130) b1130 = true := by decide +kernel

theorem c1131 : checkCell pa19 (cellAt 1131) b1131 = true := by decide +kernel

theorem c1132 : checkCell pa19 (cellAt 1132) b1132 = true := by decide +kernel

theorem c1133 : checkCell pa19 (cellAt 1133) b1133 = true := by decide +kernel

theorem c1134 : checkCell pa19 (cellAt 1134) b1134 = true := by decide +kernel

theorem slice1125 : slice 1125 10 = [cellAt 1125, cellAt 1126, cellAt 1127, cellAt 1128, cellAt 1129, cellAt 1130, cellAt 1131, cellAt 1132, cellAt 1133, cellAt 1134] := by decide +kernel

theorem batch1125_ok : checkAll pa19 (slice 1125 10) breaks1125 = true := by
  rw [slice1125]
  simp only [breaks1125, checkAll, c1125, c1126, c1127, c1128, c1129, c1130, c1131, c1132, c1133, c1134, Bool.and_self]

theorem batch1125 : ∀ c ∈ slice 1125 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1125_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1125
