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

/-! Serialized cells 145 to 154: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0145 : List ℚ := [12375/32768]
def b0146 : List ℚ := [6225/16384]
def b0147 : List ℚ := [12525/32768]
def b0148 : List ℚ := [1575/4096]
def b0149 : List ℚ := [12675/32768]
def b0150 : List ℚ := [6375/16384]
def b0151 : List ℚ := [12825/32768]
def b0152 : List ℚ := [3225/8192]
def b0153 : List ℚ := [12975/32768]
def b0154 : List ℚ := [6525/16384]

def breaks0145 : List (List ℚ) := [b0145, b0146, b0147, b0148, b0149, b0150, b0151, b0152, b0153, b0154]

theorem c0145 : checkCell pa19 (cellAt 145) b0145 = true := by decide +kernel

theorem c0146 : checkCell pa19 (cellAt 146) b0146 = true := by decide +kernel

theorem c0147 : checkCell pa19 (cellAt 147) b0147 = true := by decide +kernel

theorem c0148 : checkCell pa19 (cellAt 148) b0148 = true := by decide +kernel

theorem c0149 : checkCell pa19 (cellAt 149) b0149 = true := by decide +kernel

theorem c0150 : checkCell pa19 (cellAt 150) b0150 = true := by decide +kernel

theorem c0151 : checkCell pa19 (cellAt 151) b0151 = true := by decide +kernel

theorem c0152 : checkCell pa19 (cellAt 152) b0152 = true := by decide +kernel

theorem c0153 : checkCell pa19 (cellAt 153) b0153 = true := by decide +kernel

theorem c0154 : checkCell pa19 (cellAt 154) b0154 = true := by decide +kernel

theorem slice0145 : slice 145 10 = [cellAt 145, cellAt 146, cellAt 147, cellAt 148, cellAt 149, cellAt 150, cellAt 151, cellAt 152, cellAt 153, cellAt 154] := by decide +kernel

theorem batch0145_ok : checkAll pa19 (slice 145 10) breaks0145 = true := by
  rw [slice0145]
  simp only [breaks0145, checkAll, c0145, c0146, c0147, c0148, c0149, c0150, c0151, c0152, c0153, c0154, Bool.and_self]

theorem batch0145 : ∀ c ∈ slice 145 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0145_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0145
