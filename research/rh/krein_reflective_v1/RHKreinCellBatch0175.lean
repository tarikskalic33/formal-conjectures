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

/-! Serialized cells 175 to 184: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0175 : List ℚ := [14625/32768]
def b0176 : List ℚ := [3675/8192]
def b0177 : List ℚ := [14775/32768]
def b0178 : List ℚ := [7425/16384]
def b0179 : List ℚ := [14925/32768]
def b0180 : List ℚ := [1875/4096]
def b0181 : List ℚ := [15075/32768]
def b0182 : List ℚ := [7575/16384]
def b0183 : List ℚ := [15225/32768]
def b0184 : List ℚ := [3825/8192]

def breaks0175 : List (List ℚ) := [b0175, b0176, b0177, b0178, b0179, b0180, b0181, b0182, b0183, b0184]

theorem c0175 : checkCell pa19 (cellAt 175) b0175 = true := by decide +kernel

theorem c0176 : checkCell pa19 (cellAt 176) b0176 = true := by decide +kernel

theorem c0177 : checkCell pa19 (cellAt 177) b0177 = true := by decide +kernel

theorem c0178 : checkCell pa19 (cellAt 178) b0178 = true := by decide +kernel

theorem c0179 : checkCell pa19 (cellAt 179) b0179 = true := by decide +kernel

theorem c0180 : checkCell pa19 (cellAt 180) b0180 = true := by decide +kernel

theorem c0181 : checkCell pa19 (cellAt 181) b0181 = true := by decide +kernel

theorem c0182 : checkCell pa19 (cellAt 182) b0182 = true := by decide +kernel

theorem c0183 : checkCell pa19 (cellAt 183) b0183 = true := by decide +kernel

theorem c0184 : checkCell pa19 (cellAt 184) b0184 = true := by decide +kernel

theorem slice0175 : slice 175 10 = [cellAt 175, cellAt 176, cellAt 177, cellAt 178, cellAt 179, cellAt 180, cellAt 181, cellAt 182, cellAt 183, cellAt 184] := by decide +kernel

theorem batch0175_ok : checkAll pa19 (slice 175 10) breaks0175 = true := by
  rw [slice0175]
  simp only [breaks0175, checkAll, c0175, c0176, c0177, c0178, c0179, c0180, c0181, c0182, c0183, c0184, Bool.and_self]

theorem batch0175 : ∀ c ∈ slice 175 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0175_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0175
