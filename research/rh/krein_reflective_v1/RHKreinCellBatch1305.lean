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

/-! Serialized cells 1305 to 1314: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1305 : List ℚ := [9825/256]
def b1306 : List ℚ := [2475/64]
def b1307 : List ℚ := [9975/256]
def b1308 : List ℚ := [5025/128]
def b1309 : List ℚ := [10125/256]
def b1310 : List ℚ := [1275/32]
def b1311 : List ℚ := [10275/256]
def b1312 : List ℚ := [5175/128]
def b1313 : List ℚ := [10425/256]
def b1314 : List ℚ := [2625/64]

def breaks1305 : List (List ℚ) := [b1305, b1306, b1307, b1308, b1309, b1310, b1311, b1312, b1313, b1314]

theorem c1305 : checkCell pa19 (cellAt 1305) b1305 = true := by decide +kernel

theorem c1306 : checkCell pa19 (cellAt 1306) b1306 = true := by decide +kernel

theorem c1307 : checkCell pa19 (cellAt 1307) b1307 = true := by decide +kernel

theorem c1308 : checkCell pa19 (cellAt 1308) b1308 = true := by decide +kernel

theorem c1309 : checkCell pa19 (cellAt 1309) b1309 = true := by decide +kernel

theorem c1310 : checkCell pa19 (cellAt 1310) b1310 = true := by decide +kernel

theorem c1311 : checkCell pa19 (cellAt 1311) b1311 = true := by decide +kernel

theorem c1312 : checkCell pa19 (cellAt 1312) b1312 = true := by decide +kernel

theorem c1313 : checkCell pa19 (cellAt 1313) b1313 = true := by decide +kernel

theorem c1314 : checkCell pa19 (cellAt 1314) b1314 = true := by decide +kernel

theorem slice1305 : slice 1305 10 = [cellAt 1305, cellAt 1306, cellAt 1307, cellAt 1308, cellAt 1309, cellAt 1310, cellAt 1311, cellAt 1312, cellAt 1313, cellAt 1314] := by decide +kernel

theorem batch1305_ok : checkAll pa19 (slice 1305 10) breaks1305 = true := by
  rw [slice1305]
  simp only [breaks1305, checkAll, c1305, c1306, c1307, c1308, c1309, c1310, c1311, c1312, c1313, c1314, Bool.and_self]

theorem batch1305 : ∀ c ∈ slice 1305 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1305_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1305
