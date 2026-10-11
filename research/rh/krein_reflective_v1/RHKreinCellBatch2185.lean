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

/-! Serialized cells 2185 to 2194: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b2185 : List ℚ := [75825/256]
def b2186 : List ℚ := [18975/64]
def b2187 : List ℚ := [75975/256]
def b2188 : List ℚ := [38025/128]
def b2189 : List ℚ := [76125/256]
def b2190 : List ℚ := [152325/512, 9525/32]
def b2191 : List ℚ := [152475/512, 76275/256]
def b2192 : List ℚ := [152625/512, 38175/128]
def b2193 : List ℚ := [152775/512, 76425/256]
def b2194 : List ℚ := [152925/512, 19125/64]

def breaks2185 : List (List ℚ) := [b2185, b2186, b2187, b2188, b2189, b2190, b2191, b2192, b2193, b2194]

theorem c2185 : checkCell pa19 (cellAt 2185) b2185 = true := by decide +kernel

theorem c2186 : checkCell pa19 (cellAt 2186) b2186 = true := by decide +kernel

theorem c2187 : checkCell pa19 (cellAt 2187) b2187 = true := by decide +kernel

theorem c2188 : checkCell pa19 (cellAt 2188) b2188 = true := by decide +kernel

theorem c2189 : checkCell pa19 (cellAt 2189) b2189 = true := by decide +kernel

theorem c2190 : checkCell pa19 (cellAt 2190) b2190 = true := by decide +kernel

theorem c2191 : checkCell pa19 (cellAt 2191) b2191 = true := by decide +kernel

theorem c2192 : checkCell pa19 (cellAt 2192) b2192 = true := by decide +kernel

theorem c2193 : checkCell pa19 (cellAt 2193) b2193 = true := by decide +kernel

theorem c2194 : checkCell pa19 (cellAt 2194) b2194 = true := by decide +kernel

theorem slice2185 : slice 2185 10 = [cellAt 2185, cellAt 2186, cellAt 2187, cellAt 2188, cellAt 2189, cellAt 2190, cellAt 2191, cellAt 2192, cellAt 2193, cellAt 2194] := by decide +kernel

theorem batch2185_ok : checkAll pa19 (slice 2185 10) breaks2185 = true := by
  rw [slice2185]
  simp only [breaks2185, checkAll, c2185, c2186, c2187, c2188, c2189, c2190, c2191, c2192, c2193, c2194, Bool.and_self]

theorem batch2185 : ∀ c ∈ slice 2185 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch2185_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch2185
