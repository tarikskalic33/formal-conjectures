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

/-! Serialized cells 255 to 264: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0255 : List ℚ := [20625/32768]
def b0256 : List ℚ := [5175/8192]
def b0257 : List ℚ := [20775/32768]
def b0258 : List ℚ := [10425/16384]
def b0259 : List ℚ := [20925/32768]
def b0260 : List ℚ := [2625/4096]
def b0261 : List ℚ := [21075/32768]
def b0262 : List ℚ := [10575/16384]
def b0263 : List ℚ := [21225/32768]
def b0264 : List ℚ := [5325/8192]

def breaks0255 : List (List ℚ) := [b0255, b0256, b0257, b0258, b0259, b0260, b0261, b0262, b0263, b0264]

theorem c0255 : checkCell pa19 (cellAt 255) b0255 = true := by decide +kernel

theorem c0256 : checkCell pa19 (cellAt 256) b0256 = true := by decide +kernel

theorem c0257 : checkCell pa19 (cellAt 257) b0257 = true := by decide +kernel

theorem c0258 : checkCell pa19 (cellAt 258) b0258 = true := by decide +kernel

theorem c0259 : checkCell pa19 (cellAt 259) b0259 = true := by decide +kernel

theorem c0260 : checkCell pa19 (cellAt 260) b0260 = true := by decide +kernel

theorem c0261 : checkCell pa19 (cellAt 261) b0261 = true := by decide +kernel

theorem c0262 : checkCell pa19 (cellAt 262) b0262 = true := by decide +kernel

theorem c0263 : checkCell pa19 (cellAt 263) b0263 = true := by decide +kernel

theorem c0264 : checkCell pa19 (cellAt 264) b0264 = true := by decide +kernel

theorem slice0255 : slice 255 10 = [cellAt 255, cellAt 256, cellAt 257, cellAt 258, cellAt 259, cellAt 260, cellAt 261, cellAt 262, cellAt 263, cellAt 264] := by decide +kernel

theorem batch0255_ok : checkAll pa19 (slice 255 10) breaks0255 = true := by
  rw [slice0255]
  simp only [breaks0255, checkAll, c0255, c0256, c0257, c0258, c0259, c0260, c0261, c0262, c0263, c0264, Bool.and_self]

theorem batch0255 : ∀ c ∈ slice 255 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0255_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0255
