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

/-! Serialized cells 105 to 114: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0105 : List ℚ := [9375/32768]
def b0106 : List ℚ := [4725/16384]
def b0107 : List ℚ := [9525/32768]
def b0108 : List ℚ := [75/256]
def b0109 : List ℚ := [9675/32768]
def b0110 : List ℚ := [4875/16384]
def b0111 : List ℚ := [9825/32768]
def b0112 : List ℚ := [2475/8192]
def b0113 : List ℚ := [9975/32768]
def b0114 : List ℚ := [5025/16384]

def breaks0105 : List (List ℚ) := [b0105, b0106, b0107, b0108, b0109, b0110, b0111, b0112, b0113, b0114]

theorem c0105 : checkCell pa19 (cellAt 105) b0105 = true := by decide +kernel

theorem c0106 : checkCell pa19 (cellAt 106) b0106 = true := by decide +kernel

theorem c0107 : checkCell pa19 (cellAt 107) b0107 = true := by decide +kernel

theorem c0108 : checkCell pa19 (cellAt 108) b0108 = true := by decide +kernel

theorem c0109 : checkCell pa19 (cellAt 109) b0109 = true := by decide +kernel

theorem c0110 : checkCell pa19 (cellAt 110) b0110 = true := by decide +kernel

theorem c0111 : checkCell pa19 (cellAt 111) b0111 = true := by decide +kernel

theorem c0112 : checkCell pa19 (cellAt 112) b0112 = true := by decide +kernel

theorem c0113 : checkCell pa19 (cellAt 113) b0113 = true := by decide +kernel

theorem c0114 : checkCell pa19 (cellAt 114) b0114 = true := by decide +kernel

theorem slice0105 : slice 105 10 = [cellAt 105, cellAt 106, cellAt 107, cellAt 108, cellAt 109, cellAt 110, cellAt 111, cellAt 112, cellAt 113, cellAt 114] := by decide +kernel

theorem batch0105_ok : checkAll pa19 (slice 105 10) breaks0105 = true := by
  rw [slice0105]
  simp only [breaks0105, checkAll, c0105, c0106, c0107, c0108, c0109, c0110, c0111, c0112, c0113, c0114, Bool.and_self]

theorem batch0105 : ∀ c ∈ slice 105 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0105_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0105
