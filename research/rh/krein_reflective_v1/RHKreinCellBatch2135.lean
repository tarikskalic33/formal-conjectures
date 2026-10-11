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

/-! Serialized cells 2135 to 2144: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b2135 : List ℚ := [72075/256]
def b2136 : List ℚ := [36075/128]
def b2137 : List ℚ := [72225/256]
def b2138 : List ℚ := [18075/64]
def b2139 : List ℚ := [72375/256]
def b2140 : List ℚ := [36225/128]
def b2141 : List ℚ := [72525/256]
def b2142 : List ℚ := [9075/32]
def b2143 : List ℚ := [72675/256]
def b2144 : List ℚ := [36375/128]

def breaks2135 : List (List ℚ) := [b2135, b2136, b2137, b2138, b2139, b2140, b2141, b2142, b2143, b2144]

theorem c2135 : checkCell pa19 (cellAt 2135) b2135 = true := by decide +kernel

theorem c2136 : checkCell pa19 (cellAt 2136) b2136 = true := by decide +kernel

theorem c2137 : checkCell pa19 (cellAt 2137) b2137 = true := by decide +kernel

theorem c2138 : checkCell pa19 (cellAt 2138) b2138 = true := by decide +kernel

theorem c2139 : checkCell pa19 (cellAt 2139) b2139 = true := by decide +kernel

theorem c2140 : checkCell pa19 (cellAt 2140) b2140 = true := by decide +kernel

theorem c2141 : checkCell pa19 (cellAt 2141) b2141 = true := by decide +kernel

theorem c2142 : checkCell pa19 (cellAt 2142) b2142 = true := by decide +kernel

theorem c2143 : checkCell pa19 (cellAt 2143) b2143 = true := by decide +kernel

theorem c2144 : checkCell pa19 (cellAt 2144) b2144 = true := by decide +kernel

theorem slice2135 : slice 2135 10 = [cellAt 2135, cellAt 2136, cellAt 2137, cellAt 2138, cellAt 2139, cellAt 2140, cellAt 2141, cellAt 2142, cellAt 2143, cellAt 2144] := by decide +kernel

theorem batch2135_ok : checkAll pa19 (slice 2135 10) breaks2135 = true := by
  rw [slice2135]
  simp only [breaks2135, checkAll, c2135, c2136, c2137, c2138, c2139, c2140, c2141, c2142, c2143, c2144, Bool.and_self]

theorem batch2135 : ∀ c ∈ slice 2135 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch2135_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch2135
