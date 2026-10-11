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

/-! Serialized cells 2105 to 2114: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b2105 : List ℚ := [69825/256]
def b2106 : List ℚ := [17475/64]
def b2107 : List ℚ := [69975/256]
def b2108 : List ℚ := [35025/128]
def b2109 : List ℚ := [70125/256]
def b2110 : List ℚ := [8775/32]
def b2111 : List ℚ := [70275/256]
def b2112 : List ℚ := [35175/128]
def b2113 : List ℚ := [70425/256]
def b2114 : List ℚ := [17625/64]

def breaks2105 : List (List ℚ) := [b2105, b2106, b2107, b2108, b2109, b2110, b2111, b2112, b2113, b2114]

theorem c2105 : checkCell pa19 (cellAt 2105) b2105 = true := by decide +kernel

theorem c2106 : checkCell pa19 (cellAt 2106) b2106 = true := by decide +kernel

theorem c2107 : checkCell pa19 (cellAt 2107) b2107 = true := by decide +kernel

theorem c2108 : checkCell pa19 (cellAt 2108) b2108 = true := by decide +kernel

theorem c2109 : checkCell pa19 (cellAt 2109) b2109 = true := by decide +kernel

theorem c2110 : checkCell pa19 (cellAt 2110) b2110 = true := by decide +kernel

theorem c2111 : checkCell pa19 (cellAt 2111) b2111 = true := by decide +kernel

theorem c2112 : checkCell pa19 (cellAt 2112) b2112 = true := by decide +kernel

theorem c2113 : checkCell pa19 (cellAt 2113) b2113 = true := by decide +kernel

theorem c2114 : checkCell pa19 (cellAt 2114) b2114 = true := by decide +kernel

theorem slice2105 : slice 2105 10 = [cellAt 2105, cellAt 2106, cellAt 2107, cellAt 2108, cellAt 2109, cellAt 2110, cellAt 2111, cellAt 2112, cellAt 2113, cellAt 2114] := by decide +kernel

theorem batch2105_ok : checkAll pa19 (slice 2105 10) breaks2105 = true := by
  rw [slice2105]
  simp only [breaks2105, checkAll, c2105, c2106, c2107, c2108, c2109, c2110, c2111, c2112, c2113, c2114, Bool.and_self]

theorem batch2105 : ∀ c ∈ slice 2105 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch2105_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch2105
