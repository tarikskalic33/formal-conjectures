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

/-! Serialized cells 165 to 174: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0165 : List ℚ := [13875/32768]
def b0166 : List ℚ := [6975/16384]
def b0167 : List ℚ := [14025/32768]
def b0168 : List ℚ := [3525/8192]
def b0169 : List ℚ := [14175/32768]
def b0170 : List ℚ := [7125/16384]
def b0171 : List ℚ := [14325/32768]
def b0172 : List ℚ := [225/512]
def b0173 : List ℚ := [14475/32768]
def b0174 : List ℚ := [7275/16384]

def breaks0165 : List (List ℚ) := [b0165, b0166, b0167, b0168, b0169, b0170, b0171, b0172, b0173, b0174]

theorem c0165 : checkCell pa19 (cellAt 165) b0165 = true := by decide +kernel

theorem c0166 : checkCell pa19 (cellAt 166) b0166 = true := by decide +kernel

theorem c0167 : checkCell pa19 (cellAt 167) b0167 = true := by decide +kernel

theorem c0168 : checkCell pa19 (cellAt 168) b0168 = true := by decide +kernel

theorem c0169 : checkCell pa19 (cellAt 169) b0169 = true := by decide +kernel

theorem c0170 : checkCell pa19 (cellAt 170) b0170 = true := by decide +kernel

theorem c0171 : checkCell pa19 (cellAt 171) b0171 = true := by decide +kernel

theorem c0172 : checkCell pa19 (cellAt 172) b0172 = true := by decide +kernel

theorem c0173 : checkCell pa19 (cellAt 173) b0173 = true := by decide +kernel

theorem c0174 : checkCell pa19 (cellAt 174) b0174 = true := by decide +kernel

theorem slice0165 : slice 165 10 = [cellAt 165, cellAt 166, cellAt 167, cellAt 168, cellAt 169, cellAt 170, cellAt 171, cellAt 172, cellAt 173, cellAt 174] := by decide +kernel

theorem batch0165_ok : checkAll pa19 (slice 165 10) breaks0165 = true := by
  rw [slice0165]
  simp only [breaks0165, checkAll, c0165, c0166, c0167, c0168, c0169, c0170, c0171, c0172, c0173, c0174, Bool.and_self]

theorem batch0165 : ∀ c ∈ slice 165 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0165_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0165
