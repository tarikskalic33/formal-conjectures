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

/-! Serialized cells 215 to 224: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0215 : List ℚ := [17625/32768]
def b0216 : List ℚ := [4425/8192]
def b0217 : List ℚ := [17775/32768]
def b0218 : List ℚ := [8925/16384]
def b0219 : List ℚ := [17925/32768]
def b0220 : List ℚ := [1125/2048]
def b0221 : List ℚ := [18075/32768]
def b0222 : List ℚ := [9075/16384]
def b0223 : List ℚ := [18225/32768]
def b0224 : List ℚ := [4575/8192]

def breaks0215 : List (List ℚ) := [b0215, b0216, b0217, b0218, b0219, b0220, b0221, b0222, b0223, b0224]

theorem c0215 : checkCell pa19 (cellAt 215) b0215 = true := by decide +kernel

theorem c0216 : checkCell pa19 (cellAt 216) b0216 = true := by decide +kernel

theorem c0217 : checkCell pa19 (cellAt 217) b0217 = true := by decide +kernel

theorem c0218 : checkCell pa19 (cellAt 218) b0218 = true := by decide +kernel

theorem c0219 : checkCell pa19 (cellAt 219) b0219 = true := by decide +kernel

theorem c0220 : checkCell pa19 (cellAt 220) b0220 = true := by decide +kernel

theorem c0221 : checkCell pa19 (cellAt 221) b0221 = true := by decide +kernel

theorem c0222 : checkCell pa19 (cellAt 222) b0222 = true := by decide +kernel

theorem c0223 : checkCell pa19 (cellAt 223) b0223 = true := by decide +kernel

theorem c0224 : checkCell pa19 (cellAt 224) b0224 = true := by decide +kernel

theorem slice0215 : slice 215 10 = [cellAt 215, cellAt 216, cellAt 217, cellAt 218, cellAt 219, cellAt 220, cellAt 221, cellAt 222, cellAt 223, cellAt 224] := by decide +kernel

theorem batch0215_ok : checkAll pa19 (slice 215 10) breaks0215 = true := by
  rw [slice0215]
  simp only [breaks0215, checkAll, c0215, c0216, c0217, c0218, c0219, c0220, c0221, c0222, c0223, c0224, Bool.and_self]

theorem batch0215 : ∀ c ∈ slice 215 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0215_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0215
