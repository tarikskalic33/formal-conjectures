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

/-! Serialized cells 1075 to 1084: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1075 : List ℚ := [6375/512]
def b1076 : List ℚ := [25575/2048]
def b1077 : List ℚ := [12825/1024]
def b1078 : List ℚ := [25725/2048]
def b1079 : List ℚ := [3225/256]
def b1080 : List ℚ := [25875/2048]
def b1081 : List ℚ := [12975/1024]
def b1082 : List ℚ := [26025/2048]
def b1083 : List ℚ := [6525/512]
def b1084 : List ℚ := [26175/2048]

def breaks1075 : List (List ℚ) := [b1075, b1076, b1077, b1078, b1079, b1080, b1081, b1082, b1083, b1084]

theorem c1075 : checkCell pa19 (cellAt 1075) b1075 = true := by decide +kernel

theorem c1076 : checkCell pa19 (cellAt 1076) b1076 = true := by decide +kernel

theorem c1077 : checkCell pa19 (cellAt 1077) b1077 = true := by decide +kernel

theorem c1078 : checkCell pa19 (cellAt 1078) b1078 = true := by decide +kernel

theorem c1079 : checkCell pa19 (cellAt 1079) b1079 = true := by decide +kernel

theorem c1080 : checkCell pa19 (cellAt 1080) b1080 = true := by decide +kernel

theorem c1081 : checkCell pa19 (cellAt 1081) b1081 = true := by decide +kernel

theorem c1082 : checkCell pa19 (cellAt 1082) b1082 = true := by decide +kernel

theorem c1083 : checkCell pa19 (cellAt 1083) b1083 = true := by decide +kernel

theorem c1084 : checkCell pa19 (cellAt 1084) b1084 = true := by decide +kernel

theorem slice1075 : slice 1075 10 = [cellAt 1075, cellAt 1076, cellAt 1077, cellAt 1078, cellAt 1079, cellAt 1080, cellAt 1081, cellAt 1082, cellAt 1083, cellAt 1084] := by decide +kernel

theorem batch1075_ok : checkAll pa19 (slice 1075 10) breaks1075 = true := by
  rw [slice1075]
  simp only [breaks1075, checkAll, c1075, c1076, c1077, c1078, c1079, c1080, c1081, c1082, c1083, c1084, Bool.and_self]

theorem batch1075 : ∀ c ∈ slice 1075 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1075_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1075
