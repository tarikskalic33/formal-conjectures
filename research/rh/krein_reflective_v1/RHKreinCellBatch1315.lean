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

/-! Serialized cells 1315 to 1324: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1315 : List ℚ := [10575/256]
def b1316 : List ℚ := [5325/128]
def b1317 : List ℚ := [10725/256]
def b1318 : List ℚ := [675/16]
def b1319 : List ℚ := [10875/256]
def b1320 : List ℚ := [5475/128]
def b1321 : List ℚ := [11025/256]
def b1322 : List ℚ := [2775/64]
def b1323 : List ℚ := [11175/256]
def b1324 : List ℚ := [5625/128]

def breaks1315 : List (List ℚ) := [b1315, b1316, b1317, b1318, b1319, b1320, b1321, b1322, b1323, b1324]

theorem c1315 : checkCell pa19 (cellAt 1315) b1315 = true := by decide +kernel

theorem c1316 : checkCell pa19 (cellAt 1316) b1316 = true := by decide +kernel

theorem c1317 : checkCell pa19 (cellAt 1317) b1317 = true := by decide +kernel

theorem c1318 : checkCell pa19 (cellAt 1318) b1318 = true := by decide +kernel

theorem c1319 : checkCell pa19 (cellAt 1319) b1319 = true := by decide +kernel

theorem c1320 : checkCell pa19 (cellAt 1320) b1320 = true := by decide +kernel

theorem c1321 : checkCell pa19 (cellAt 1321) b1321 = true := by decide +kernel

theorem c1322 : checkCell pa19 (cellAt 1322) b1322 = true := by decide +kernel

theorem c1323 : checkCell pa19 (cellAt 1323) b1323 = true := by decide +kernel

theorem c1324 : checkCell pa19 (cellAt 1324) b1324 = true := by decide +kernel

theorem slice1315 : slice 1315 10 = [cellAt 1315, cellAt 1316, cellAt 1317, cellAt 1318, cellAt 1319, cellAt 1320, cellAt 1321, cellAt 1322, cellAt 1323, cellAt 1324] := by decide +kernel

theorem batch1315_ok : checkAll pa19 (slice 1315 10) breaks1315 = true := by
  rw [slice1315]
  simp only [breaks1315, checkAll, c1315, c1316, c1317, c1318, c1319, c1320, c1321, c1322, c1323, c1324, Bool.and_self]

theorem batch1315 : ∀ c ∈ slice 1315 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1315_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1315
