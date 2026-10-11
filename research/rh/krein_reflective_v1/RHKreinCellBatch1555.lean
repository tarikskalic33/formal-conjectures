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

/-! Serialized cells 1555 to 1564: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1555 : List ℚ := [28575/256]
def b1556 : List ℚ := [14325/128]
def b1557 : List ℚ := [28725/256]
def b1558 : List ℚ := [225/2]
def b1559 : List ℚ := [28875/256]
def b1560 : List ℚ := [14475/128]
def b1561 : List ℚ := [29025/256]
def b1562 : List ℚ := [7275/64]
def b1563 : List ℚ := [29175/256]
def b1564 : List ℚ := [14625/128]

def breaks1555 : List (List ℚ) := [b1555, b1556, b1557, b1558, b1559, b1560, b1561, b1562, b1563, b1564]

theorem c1555 : checkCell pa19 (cellAt 1555) b1555 = true := by decide +kernel

theorem c1556 : checkCell pa19 (cellAt 1556) b1556 = true := by decide +kernel

theorem c1557 : checkCell pa19 (cellAt 1557) b1557 = true := by decide +kernel

theorem c1558 : checkCell pa19 (cellAt 1558) b1558 = true := by decide +kernel

theorem c1559 : checkCell pa19 (cellAt 1559) b1559 = true := by decide +kernel

theorem c1560 : checkCell pa19 (cellAt 1560) b1560 = true := by decide +kernel

theorem c1561 : checkCell pa19 (cellAt 1561) b1561 = true := by decide +kernel

theorem c1562 : checkCell pa19 (cellAt 1562) b1562 = true := by decide +kernel

theorem c1563 : checkCell pa19 (cellAt 1563) b1563 = true := by decide +kernel

theorem c1564 : checkCell pa19 (cellAt 1564) b1564 = true := by decide +kernel

theorem slice1555 : slice 1555 10 = [cellAt 1555, cellAt 1556, cellAt 1557, cellAt 1558, cellAt 1559, cellAt 1560, cellAt 1561, cellAt 1562, cellAt 1563, cellAt 1564] := by decide +kernel

theorem batch1555_ok : checkAll pa19 (slice 1555 10) breaks1555 = true := by
  rw [slice1555]
  simp only [breaks1555, checkAll, c1555, c1556, c1557, c1558, c1559, c1560, c1561, c1562, c1563, c1564, Bool.and_self]

theorem batch1555 : ∀ c ∈ slice 1555 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1555_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1555
