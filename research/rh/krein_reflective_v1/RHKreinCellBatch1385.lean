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

/-! Serialized cells 1385 to 1394: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1385 : List ℚ := [15825/256]
def b1386 : List ℚ := [3975/64]
def b1387 : List ℚ := [15975/256]
def b1388 : List ℚ := [8025/128]
def b1389 : List ℚ := [16125/256]
def b1390 : List ℚ := [2025/32]
def b1391 : List ℚ := [16275/256]
def b1392 : List ℚ := [8175/128]
def b1393 : List ℚ := [16425/256]
def b1394 : List ℚ := [4125/64]

def breaks1385 : List (List ℚ) := [b1385, b1386, b1387, b1388, b1389, b1390, b1391, b1392, b1393, b1394]

theorem c1385 : checkCell pa19 (cellAt 1385) b1385 = true := by decide +kernel

theorem c1386 : checkCell pa19 (cellAt 1386) b1386 = true := by decide +kernel

theorem c1387 : checkCell pa19 (cellAt 1387) b1387 = true := by decide +kernel

theorem c1388 : checkCell pa19 (cellAt 1388) b1388 = true := by decide +kernel

theorem c1389 : checkCell pa19 (cellAt 1389) b1389 = true := by decide +kernel

theorem c1390 : checkCell pa19 (cellAt 1390) b1390 = true := by decide +kernel

theorem c1391 : checkCell pa19 (cellAt 1391) b1391 = true := by decide +kernel

theorem c1392 : checkCell pa19 (cellAt 1392) b1392 = true := by decide +kernel

theorem c1393 : checkCell pa19 (cellAt 1393) b1393 = true := by decide +kernel

theorem c1394 : checkCell pa19 (cellAt 1394) b1394 = true := by decide +kernel

theorem slice1385 : slice 1385 10 = [cellAt 1385, cellAt 1386, cellAt 1387, cellAt 1388, cellAt 1389, cellAt 1390, cellAt 1391, cellAt 1392, cellAt 1393, cellAt 1394] := by decide +kernel

theorem batch1385_ok : checkAll pa19 (slice 1385 10) breaks1385 = true := by
  rw [slice1385]
  simp only [breaks1385, checkAll, c1385, c1386, c1387, c1388, c1389, c1390, c1391, c1392, c1393, c1394, Bool.and_self]

theorem batch1385 : ∀ c ∈ slice 1385 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1385_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1385
