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

/-! Serialized cells 1465 to 1474: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1465 : List ℚ := [21825/256]
def b1466 : List ℚ := [5475/64]
def b1467 : List ℚ := [21975/256]
def b1468 : List ℚ := [11025/128]
def b1469 : List ℚ := [22125/256]
def b1470 : List ℚ := [2775/32]
def b1471 : List ℚ := [22275/256]
def b1472 : List ℚ := [11175/128]
def b1473 : List ℚ := [22425/256]
def b1474 : List ℚ := [5625/64]

def breaks1465 : List (List ℚ) := [b1465, b1466, b1467, b1468, b1469, b1470, b1471, b1472, b1473, b1474]

theorem c1465 : checkCell pa19 (cellAt 1465) b1465 = true := by decide +kernel

theorem c1466 : checkCell pa19 (cellAt 1466) b1466 = true := by decide +kernel

theorem c1467 : checkCell pa19 (cellAt 1467) b1467 = true := by decide +kernel

theorem c1468 : checkCell pa19 (cellAt 1468) b1468 = true := by decide +kernel

theorem c1469 : checkCell pa19 (cellAt 1469) b1469 = true := by decide +kernel

theorem c1470 : checkCell pa19 (cellAt 1470) b1470 = true := by decide +kernel

theorem c1471 : checkCell pa19 (cellAt 1471) b1471 = true := by decide +kernel

theorem c1472 : checkCell pa19 (cellAt 1472) b1472 = true := by decide +kernel

theorem c1473 : checkCell pa19 (cellAt 1473) b1473 = true := by decide +kernel

theorem c1474 : checkCell pa19 (cellAt 1474) b1474 = true := by decide +kernel

theorem slice1465 : slice 1465 10 = [cellAt 1465, cellAt 1466, cellAt 1467, cellAt 1468, cellAt 1469, cellAt 1470, cellAt 1471, cellAt 1472, cellAt 1473, cellAt 1474] := by decide +kernel

theorem batch1465_ok : checkAll pa19 (slice 1465 10) breaks1465 = true := by
  rw [slice1465]
  simp only [breaks1465, checkAll, c1465, c1466, c1467, c1468, c1469, c1470, c1471, c1472, c1473, c1474, Bool.and_self]

theorem batch1465 : ∀ c ∈ slice 1465 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1465_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1465
