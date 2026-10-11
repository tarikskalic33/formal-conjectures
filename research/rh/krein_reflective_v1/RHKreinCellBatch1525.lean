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

/-! Serialized cells 1525 to 1534: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1525 : List ℚ := [26325/256]
def b1526 : List ℚ := [825/8]
def b1527 : List ℚ := [26475/256]
def b1528 : List ℚ := [13275/128]
def b1529 : List ℚ := [26625/256]
def b1530 : List ℚ := [6675/64]
def b1531 : List ℚ := [26775/256]
def b1532 : List ℚ := [13425/128]
def b1533 : List ℚ := [26925/256]
def b1534 : List ℚ := [3375/32]

def breaks1525 : List (List ℚ) := [b1525, b1526, b1527, b1528, b1529, b1530, b1531, b1532, b1533, b1534]

theorem c1525 : checkCell pa19 (cellAt 1525) b1525 = true := by decide +kernel

theorem c1526 : checkCell pa19 (cellAt 1526) b1526 = true := by decide +kernel

theorem c1527 : checkCell pa19 (cellAt 1527) b1527 = true := by decide +kernel

theorem c1528 : checkCell pa19 (cellAt 1528) b1528 = true := by decide +kernel

theorem c1529 : checkCell pa19 (cellAt 1529) b1529 = true := by decide +kernel

theorem c1530 : checkCell pa19 (cellAt 1530) b1530 = true := by decide +kernel

theorem c1531 : checkCell pa19 (cellAt 1531) b1531 = true := by decide +kernel

theorem c1532 : checkCell pa19 (cellAt 1532) b1532 = true := by decide +kernel

theorem c1533 : checkCell pa19 (cellAt 1533) b1533 = true := by decide +kernel

theorem c1534 : checkCell pa19 (cellAt 1534) b1534 = true := by decide +kernel

theorem slice1525 : slice 1525 10 = [cellAt 1525, cellAt 1526, cellAt 1527, cellAt 1528, cellAt 1529, cellAt 1530, cellAt 1531, cellAt 1532, cellAt 1533, cellAt 1534] := by decide +kernel

theorem batch1525_ok : checkAll pa19 (slice 1525 10) breaks1525 = true := by
  rw [slice1525]
  simp only [breaks1525, checkAll, c1525, c1526, c1527, c1528, c1529, c1530, c1531, c1532, c1533, c1534, Bool.and_self]

theorem batch1525 : ∀ c ∈ slice 1525 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1525_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1525
