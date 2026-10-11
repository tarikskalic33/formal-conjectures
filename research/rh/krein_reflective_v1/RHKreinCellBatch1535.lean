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

/-! Serialized cells 1535 to 1544: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1535 : List ℚ := [27075/256]
def b1536 : List ℚ := [13575/128]
def b1537 : List ℚ := [27225/256]
def b1538 : List ℚ := [6825/64]
def b1539 : List ℚ := [27375/256]
def b1540 : List ℚ := [13725/128]
def b1541 : List ℚ := [27525/256]
def b1542 : List ℚ := [1725/16]
def b1543 : List ℚ := [27675/256]
def b1544 : List ℚ := [13875/128]

def breaks1535 : List (List ℚ) := [b1535, b1536, b1537, b1538, b1539, b1540, b1541, b1542, b1543, b1544]

theorem c1535 : checkCell pa19 (cellAt 1535) b1535 = true := by decide +kernel

theorem c1536 : checkCell pa19 (cellAt 1536) b1536 = true := by decide +kernel

theorem c1537 : checkCell pa19 (cellAt 1537) b1537 = true := by decide +kernel

theorem c1538 : checkCell pa19 (cellAt 1538) b1538 = true := by decide +kernel

theorem c1539 : checkCell pa19 (cellAt 1539) b1539 = true := by decide +kernel

theorem c1540 : checkCell pa19 (cellAt 1540) b1540 = true := by decide +kernel

theorem c1541 : checkCell pa19 (cellAt 1541) b1541 = true := by decide +kernel

theorem c1542 : checkCell pa19 (cellAt 1542) b1542 = true := by decide +kernel

theorem c1543 : checkCell pa19 (cellAt 1543) b1543 = true := by decide +kernel

theorem c1544 : checkCell pa19 (cellAt 1544) b1544 = true := by decide +kernel

theorem slice1535 : slice 1535 10 = [cellAt 1535, cellAt 1536, cellAt 1537, cellAt 1538, cellAt 1539, cellAt 1540, cellAt 1541, cellAt 1542, cellAt 1543, cellAt 1544] := by decide +kernel

theorem batch1535_ok : checkAll pa19 (slice 1535 10) breaks1535 = true := by
  rw [slice1535]
  simp only [breaks1535, checkAll, c1535, c1536, c1537, c1538, c1539, c1540, c1541, c1542, c1543, c1544, Bool.and_self]

theorem batch1535 : ∀ c ∈ slice 1535 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1535_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1535
