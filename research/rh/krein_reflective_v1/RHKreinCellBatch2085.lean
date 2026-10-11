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

/-! Serialized cells 2085 to 2094: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b2085 : List ℚ := [68325/256]
def b2086 : List ℚ := [4275/16]
def b2087 : List ℚ := [68475/256]
def b2088 : List ℚ := [34275/128]
def b2089 : List ℚ := [68625/256]
def b2090 : List ℚ := [17175/64]
def b2091 : List ℚ := [68775/256]
def b2092 : List ℚ := [34425/128]
def b2093 : List ℚ := [68925/256]
def b2094 : List ℚ := [8625/32]

def breaks2085 : List (List ℚ) := [b2085, b2086, b2087, b2088, b2089, b2090, b2091, b2092, b2093, b2094]

theorem c2085 : checkCell pa19 (cellAt 2085) b2085 = true := by decide +kernel

theorem c2086 : checkCell pa19 (cellAt 2086) b2086 = true := by decide +kernel

theorem c2087 : checkCell pa19 (cellAt 2087) b2087 = true := by decide +kernel

theorem c2088 : checkCell pa19 (cellAt 2088) b2088 = true := by decide +kernel

theorem c2089 : checkCell pa19 (cellAt 2089) b2089 = true := by decide +kernel

theorem c2090 : checkCell pa19 (cellAt 2090) b2090 = true := by decide +kernel

theorem c2091 : checkCell pa19 (cellAt 2091) b2091 = true := by decide +kernel

theorem c2092 : checkCell pa19 (cellAt 2092) b2092 = true := by decide +kernel

theorem c2093 : checkCell pa19 (cellAt 2093) b2093 = true := by decide +kernel

theorem c2094 : checkCell pa19 (cellAt 2094) b2094 = true := by decide +kernel

theorem slice2085 : slice 2085 10 = [cellAt 2085, cellAt 2086, cellAt 2087, cellAt 2088, cellAt 2089, cellAt 2090, cellAt 2091, cellAt 2092, cellAt 2093, cellAt 2094] := by decide +kernel

theorem batch2085_ok : checkAll pa19 (slice 2085 10) breaks2085 = true := by
  rw [slice2085]
  simp only [breaks2085, checkAll, c2085, c2086, c2087, c2088, c2089, c2090, c2091, c2092, c2093, c2094, Bool.and_self]

theorem batch2085 : ∀ c ∈ slice 2085 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch2085_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch2085
