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

/-! Serialized cells 1265 to 1274: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1265 : List ℚ := [14925/512, 1875/64]
def b1266 : List ℚ := [7575/256]
def b1267 : List ℚ := [3825/128]
def b1268 : List ℚ := [7725/256]
def b1269 : List ℚ := [975/32]
def b1270 : List ℚ := [7875/256]
def b1271 : List ℚ := [3975/128]
def b1272 : List ℚ := [8025/256]
def b1273 : List ℚ := [2025/64]
def b1274 : List ℚ := [8175/256]

def breaks1265 : List (List ℚ) := [b1265, b1266, b1267, b1268, b1269, b1270, b1271, b1272, b1273, b1274]

theorem c1265 : checkCell pa19 (cellAt 1265) b1265 = true := by decide +kernel

theorem c1266 : checkCell pa19 (cellAt 1266) b1266 = true := by decide +kernel

theorem c1267 : checkCell pa19 (cellAt 1267) b1267 = true := by decide +kernel

theorem c1268 : checkCell pa19 (cellAt 1268) b1268 = true := by decide +kernel

theorem c1269 : checkCell pa19 (cellAt 1269) b1269 = true := by decide +kernel

theorem c1270 : checkCell pa19 (cellAt 1270) b1270 = true := by decide +kernel

theorem c1271 : checkCell pa19 (cellAt 1271) b1271 = true := by decide +kernel

theorem c1272 : checkCell pa19 (cellAt 1272) b1272 = true := by decide +kernel

theorem c1273 : checkCell pa19 (cellAt 1273) b1273 = true := by decide +kernel

theorem c1274 : checkCell pa19 (cellAt 1274) b1274 = true := by decide +kernel

theorem slice1265 : slice 1265 10 = [cellAt 1265, cellAt 1266, cellAt 1267, cellAt 1268, cellAt 1269, cellAt 1270, cellAt 1271, cellAt 1272, cellAt 1273, cellAt 1274] := by decide +kernel

theorem batch1265_ok : checkAll pa19 (slice 1265 10) breaks1265 = true := by
  rw [slice1265]
  simp only [breaks1265, checkAll, c1265, c1266, c1267, c1268, c1269, c1270, c1271, c1272, c1273, c1274, Bool.and_self]

theorem batch1265 : ∀ c ∈ slice 1265 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1265_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1265
