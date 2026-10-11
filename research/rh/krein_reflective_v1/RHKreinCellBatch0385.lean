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

/-! Serialized cells 385 to 394: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0385 : List ℚ := [30375/32768]
def b0386 : List ℚ := [15225/16384]
def b0387 : List ℚ := [30525/32768]
def b0388 : List ℚ := [3825/4096]
def b0389 : List ℚ := [30675/32768]
def b0390 : List ℚ := [15375/16384]
def b0391 : List ℚ := [30825/32768]
def b0392 : List ℚ := [7725/8192]
def b0393 : List ℚ := [30975/32768]
def b0394 : List ℚ := [15525/16384]

def breaks0385 : List (List ℚ) := [b0385, b0386, b0387, b0388, b0389, b0390, b0391, b0392, b0393, b0394]

theorem c0385 : checkCell pa19 (cellAt 385) b0385 = true := by decide +kernel

theorem c0386 : checkCell pa19 (cellAt 386) b0386 = true := by decide +kernel

theorem c0387 : checkCell pa19 (cellAt 387) b0387 = true := by decide +kernel

theorem c0388 : checkCell pa19 (cellAt 388) b0388 = true := by decide +kernel

theorem c0389 : checkCell pa19 (cellAt 389) b0389 = true := by decide +kernel

theorem c0390 : checkCell pa19 (cellAt 390) b0390 = true := by decide +kernel

theorem c0391 : checkCell pa19 (cellAt 391) b0391 = true := by decide +kernel

theorem c0392 : checkCell pa19 (cellAt 392) b0392 = true := by decide +kernel

theorem c0393 : checkCell pa19 (cellAt 393) b0393 = true := by decide +kernel

theorem c0394 : checkCell pa19 (cellAt 394) b0394 = true := by decide +kernel

theorem slice0385 : slice 385 10 = [cellAt 385, cellAt 386, cellAt 387, cellAt 388, cellAt 389, cellAt 390, cellAt 391, cellAt 392, cellAt 393, cellAt 394] := by decide +kernel

theorem batch0385_ok : checkAll pa19 (slice 385 10) breaks0385 = true := by
  rw [slice0385]
  simp only [breaks0385, checkAll, c0385, c0386, c0387, c0388, c0389, c0390, c0391, c0392, c0393, c0394, Bool.and_self]

theorem batch0385 : ∀ c ∈ slice 385 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0385_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0385
