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

/-! Serialized cells 485 to 494: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0485 : List ℚ := [37875/32768]
def b0486 : List ℚ := [18975/16384]
def b0487 : List ℚ := [38025/32768]
def b0488 : List ℚ := [9525/8192]
def b0489 : List ℚ := [38175/32768]
def b0490 : List ℚ := [19125/16384]
def b0491 : List ℚ := [38325/32768]
def b0492 : List ℚ := [75/64]
def b0493 : List ℚ := [38475/32768]
def b0494 : List ℚ := [19275/16384]

def breaks0485 : List (List ℚ) := [b0485, b0486, b0487, b0488, b0489, b0490, b0491, b0492, b0493, b0494]

theorem c0485 : checkCell pa19 (cellAt 485) b0485 = true := by decide +kernel

theorem c0486 : checkCell pa19 (cellAt 486) b0486 = true := by decide +kernel

theorem c0487 : checkCell pa19 (cellAt 487) b0487 = true := by decide +kernel

theorem c0488 : checkCell pa19 (cellAt 488) b0488 = true := by decide +kernel

theorem c0489 : checkCell pa19 (cellAt 489) b0489 = true := by decide +kernel

theorem c0490 : checkCell pa19 (cellAt 490) b0490 = true := by decide +kernel

theorem c0491 : checkCell pa19 (cellAt 491) b0491 = true := by decide +kernel

theorem c0492 : checkCell pa19 (cellAt 492) b0492 = true := by decide +kernel

theorem c0493 : checkCell pa19 (cellAt 493) b0493 = true := by decide +kernel

theorem c0494 : checkCell pa19 (cellAt 494) b0494 = true := by decide +kernel

theorem slice0485 : slice 485 10 = [cellAt 485, cellAt 486, cellAt 487, cellAt 488, cellAt 489, cellAt 490, cellAt 491, cellAt 492, cellAt 493, cellAt 494] := by decide +kernel

theorem batch0485_ok : checkAll pa19 (slice 485 10) breaks0485 = true := by
  rw [slice0485]
  simp only [breaks0485, checkAll, c0485, c0486, c0487, c0488, c0489, c0490, c0491, c0492, c0493, c0494, Bool.and_self]

theorem batch0485 : ∀ c ∈ slice 485 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0485_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0485
