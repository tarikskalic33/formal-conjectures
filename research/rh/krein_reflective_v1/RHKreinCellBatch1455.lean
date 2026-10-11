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

/-! Serialized cells 1455 to 1464: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1455 : List ℚ := [42075/512, 21075/256]
def b1456 : List ℚ := [42225/512, 10575/128]
def b1457 : List ℚ := [42375/512, 21225/256]
def b1458 : List ℚ := [42525/512, 5325/64]
def b1459 : List ℚ := [42675/512, 21375/256]
def b1460 : List ℚ := [42825/512, 10725/128]
def b1461 : List ℚ := [21525/256]
def b1462 : List ℚ := [675/8]
def b1463 : List ℚ := [21675/256]
def b1464 : List ℚ := [10875/128]

def breaks1455 : List (List ℚ) := [b1455, b1456, b1457, b1458, b1459, b1460, b1461, b1462, b1463, b1464]

theorem c1455 : checkCell pa19 (cellAt 1455) b1455 = true := by decide +kernel

theorem c1456 : checkCell pa19 (cellAt 1456) b1456 = true := by decide +kernel

theorem c1457 : checkCell pa19 (cellAt 1457) b1457 = true := by decide +kernel

theorem c1458 : checkCell pa19 (cellAt 1458) b1458 = true := by decide +kernel

theorem c1459 : checkCell pa19 (cellAt 1459) b1459 = true := by decide +kernel

theorem c1460 : checkCell pa19 (cellAt 1460) b1460 = true := by decide +kernel

theorem c1461 : checkCell pa19 (cellAt 1461) b1461 = true := by decide +kernel

theorem c1462 : checkCell pa19 (cellAt 1462) b1462 = true := by decide +kernel

theorem c1463 : checkCell pa19 (cellAt 1463) b1463 = true := by decide +kernel

theorem c1464 : checkCell pa19 (cellAt 1464) b1464 = true := by decide +kernel

theorem slice1455 : slice 1455 10 = [cellAt 1455, cellAt 1456, cellAt 1457, cellAt 1458, cellAt 1459, cellAt 1460, cellAt 1461, cellAt 1462, cellAt 1463, cellAt 1464] := by decide +kernel

theorem batch1455_ok : checkAll pa19 (slice 1455 10) breaks1455 = true := by
  rw [slice1455]
  simp only [breaks1455, checkAll, c1455, c1456, c1457, c1458, c1459, c1460, c1461, c1462, c1463, c1464, Bool.and_self]

theorem batch1455 : ∀ c ∈ slice 1455 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1455_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1455
