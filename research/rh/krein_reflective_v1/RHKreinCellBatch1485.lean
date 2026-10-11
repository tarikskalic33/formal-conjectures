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

/-! Serialized cells 1485 to 1494: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1485 : List ℚ := [46575/512, 23325/256]
def b1486 : List ℚ := [46725/512, 2925/32]
def b1487 : List ℚ := [46875/512, 23475/256]
def b1488 : List ℚ := [11775/128]
def b1489 : List ℚ := [23625/256]
def b1490 : List ℚ := [5925/64]
def b1491 : List ℚ := [23775/256]
def b1492 : List ℚ := [11925/128]
def b1493 : List ℚ := [23925/256]
def b1494 : List ℚ := [375/4]

def breaks1485 : List (List ℚ) := [b1485, b1486, b1487, b1488, b1489, b1490, b1491, b1492, b1493, b1494]

theorem c1485 : checkCell pa19 (cellAt 1485) b1485 = true := by decide +kernel

theorem c1486 : checkCell pa19 (cellAt 1486) b1486 = true := by decide +kernel

theorem c1487 : checkCell pa19 (cellAt 1487) b1487 = true := by decide +kernel

theorem c1488 : checkCell pa19 (cellAt 1488) b1488 = true := by decide +kernel

theorem c1489 : checkCell pa19 (cellAt 1489) b1489 = true := by decide +kernel

theorem c1490 : checkCell pa19 (cellAt 1490) b1490 = true := by decide +kernel

theorem c1491 : checkCell pa19 (cellAt 1491) b1491 = true := by decide +kernel

theorem c1492 : checkCell pa19 (cellAt 1492) b1492 = true := by decide +kernel

theorem c1493 : checkCell pa19 (cellAt 1493) b1493 = true := by decide +kernel

theorem c1494 : checkCell pa19 (cellAt 1494) b1494 = true := by decide +kernel

theorem slice1485 : slice 1485 10 = [cellAt 1485, cellAt 1486, cellAt 1487, cellAt 1488, cellAt 1489, cellAt 1490, cellAt 1491, cellAt 1492, cellAt 1493, cellAt 1494] := by decide +kernel

theorem batch1485_ok : checkAll pa19 (slice 1485 10) breaks1485 = true := by
  rw [slice1485]
  simp only [breaks1485, checkAll, c1485, c1486, c1487, c1488, c1489, c1490, c1491, c1492, c1493, c1494, Bool.and_self]

theorem batch1485 : ∀ c ∈ slice 1485 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1485_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1485
