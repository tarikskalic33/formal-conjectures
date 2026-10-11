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

/-! Serialized cells 2175 to 2184: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b2175 : List ℚ := [75075/256]
def b2176 : List ℚ := [37575/128]
def b2177 : List ℚ := [75225/256]
def b2178 : List ℚ := [18825/64]
def b2179 : List ℚ := [75375/256]
def b2180 : List ℚ := [37725/128]
def b2181 : List ℚ := [75525/256]
def b2182 : List ℚ := [4725/16]
def b2183 : List ℚ := [75675/256]
def b2184 : List ℚ := [37875/128]

def breaks2175 : List (List ℚ) := [b2175, b2176, b2177, b2178, b2179, b2180, b2181, b2182, b2183, b2184]

theorem c2175 : checkCell pa19 (cellAt 2175) b2175 = true := by decide +kernel

theorem c2176 : checkCell pa19 (cellAt 2176) b2176 = true := by decide +kernel

theorem c2177 : checkCell pa19 (cellAt 2177) b2177 = true := by decide +kernel

theorem c2178 : checkCell pa19 (cellAt 2178) b2178 = true := by decide +kernel

theorem c2179 : checkCell pa19 (cellAt 2179) b2179 = true := by decide +kernel

theorem c2180 : checkCell pa19 (cellAt 2180) b2180 = true := by decide +kernel

theorem c2181 : checkCell pa19 (cellAt 2181) b2181 = true := by decide +kernel

theorem c2182 : checkCell pa19 (cellAt 2182) b2182 = true := by decide +kernel

theorem c2183 : checkCell pa19 (cellAt 2183) b2183 = true := by decide +kernel

theorem c2184 : checkCell pa19 (cellAt 2184) b2184 = true := by decide +kernel

theorem slice2175 : slice 2175 10 = [cellAt 2175, cellAt 2176, cellAt 2177, cellAt 2178, cellAt 2179, cellAt 2180, cellAt 2181, cellAt 2182, cellAt 2183, cellAt 2184] := by decide +kernel

theorem batch2175_ok : checkAll pa19 (slice 2175 10) breaks2175 = true := by
  rw [slice2175]
  simp only [breaks2175, checkAll, c2175, c2176, c2177, c2178, c2179, c2180, c2181, c2182, c2183, c2184, Bool.and_self]

theorem batch2175 : ∀ c ∈ slice 2175 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch2175_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch2175
