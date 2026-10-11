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

/-! Serialized cells 515 to 524: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0515 : List ℚ := [40125/32768]
def b0516 : List ℚ := [5025/4096]
def b0517 : List ℚ := [40275/32768]
def b0518 : List ℚ := [20175/16384]
def b0519 : List ℚ := [40425/32768]
def b0520 : List ℚ := [10125/8192]
def b0521 : List ℚ := [40575/32768]
def b0522 : List ℚ := [20325/16384]
def b0523 : List ℚ := [40725/32768]
def b0524 : List ℚ := [1275/1024]

def breaks0515 : List (List ℚ) := [b0515, b0516, b0517, b0518, b0519, b0520, b0521, b0522, b0523, b0524]

theorem c0515 : checkCell pa19 (cellAt 515) b0515 = true := by decide +kernel

theorem c0516 : checkCell pa19 (cellAt 516) b0516 = true := by decide +kernel

theorem c0517 : checkCell pa19 (cellAt 517) b0517 = true := by decide +kernel

theorem c0518 : checkCell pa19 (cellAt 518) b0518 = true := by decide +kernel

theorem c0519 : checkCell pa19 (cellAt 519) b0519 = true := by decide +kernel

theorem c0520 : checkCell pa19 (cellAt 520) b0520 = true := by decide +kernel

theorem c0521 : checkCell pa19 (cellAt 521) b0521 = true := by decide +kernel

theorem c0522 : checkCell pa19 (cellAt 522) b0522 = true := by decide +kernel

theorem c0523 : checkCell pa19 (cellAt 523) b0523 = true := by decide +kernel

theorem c0524 : checkCell pa19 (cellAt 524) b0524 = true := by decide +kernel

theorem slice0515 : slice 515 10 = [cellAt 515, cellAt 516, cellAt 517, cellAt 518, cellAt 519, cellAt 520, cellAt 521, cellAt 522, cellAt 523, cellAt 524] := by decide +kernel

theorem batch0515_ok : checkAll pa19 (slice 515 10) breaks0515 = true := by
  rw [slice0515]
  simp only [breaks0515, checkAll, c0515, c0516, c0517, c0518, c0519, c0520, c0521, c0522, c0523, c0524, Bool.and_self]

theorem batch0515 : ∀ c ∈ slice 515 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0515_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0515
