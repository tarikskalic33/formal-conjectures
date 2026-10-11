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

/-! Serialized cells 2115 to 2124: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b2115 : List ℚ := [70575/256]
def b2116 : List ℚ := [35325/128]
def b2117 : List ℚ := [70725/256]
def b2118 : List ℚ := [4425/16]
def b2119 : List ℚ := [70875/256]
def b2120 : List ℚ := [35475/128]
def b2121 : List ℚ := [71025/256]
def b2122 : List ℚ := [17775/64]
def b2123 : List ℚ := [71175/256]
def b2124 : List ℚ := [35625/128]

def breaks2115 : List (List ℚ) := [b2115, b2116, b2117, b2118, b2119, b2120, b2121, b2122, b2123, b2124]

theorem c2115 : checkCell pa19 (cellAt 2115) b2115 = true := by decide +kernel

theorem c2116 : checkCell pa19 (cellAt 2116) b2116 = true := by decide +kernel

theorem c2117 : checkCell pa19 (cellAt 2117) b2117 = true := by decide +kernel

theorem c2118 : checkCell pa19 (cellAt 2118) b2118 = true := by decide +kernel

theorem c2119 : checkCell pa19 (cellAt 2119) b2119 = true := by decide +kernel

theorem c2120 : checkCell pa19 (cellAt 2120) b2120 = true := by decide +kernel

theorem c2121 : checkCell pa19 (cellAt 2121) b2121 = true := by decide +kernel

theorem c2122 : checkCell pa19 (cellAt 2122) b2122 = true := by decide +kernel

theorem c2123 : checkCell pa19 (cellAt 2123) b2123 = true := by decide +kernel

theorem c2124 : checkCell pa19 (cellAt 2124) b2124 = true := by decide +kernel

theorem slice2115 : slice 2115 10 = [cellAt 2115, cellAt 2116, cellAt 2117, cellAt 2118, cellAt 2119, cellAt 2120, cellAt 2121, cellAt 2122, cellAt 2123, cellAt 2124] := by decide +kernel

theorem batch2115_ok : checkAll pa19 (slice 2115 10) breaks2115 = true := by
  rw [slice2115]
  simp only [breaks2115, checkAll, c2115, c2116, c2117, c2118, c2119, c2120, c2121, c2122, c2123, c2124, Bool.and_self]

theorem batch2115 : ∀ c ∈ slice 2115 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch2115_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch2115
