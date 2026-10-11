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

/-! Serialized cells 475 to 484: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0475 : List ℚ := [37125/32768]
def b0476 : List ℚ := [2325/2048]
def b0477 : List ℚ := [37275/32768]
def b0478 : List ℚ := [18675/16384]
def b0479 : List ℚ := [37425/32768]
def b0480 : List ℚ := [9375/8192]
def b0481 : List ℚ := [37575/32768]
def b0482 : List ℚ := [18825/16384]
def b0483 : List ℚ := [37725/32768]
def b0484 : List ℚ := [4725/4096]

def breaks0475 : List (List ℚ) := [b0475, b0476, b0477, b0478, b0479, b0480, b0481, b0482, b0483, b0484]

theorem c0475 : checkCell pa19 (cellAt 475) b0475 = true := by decide +kernel

theorem c0476 : checkCell pa19 (cellAt 476) b0476 = true := by decide +kernel

theorem c0477 : checkCell pa19 (cellAt 477) b0477 = true := by decide +kernel

theorem c0478 : checkCell pa19 (cellAt 478) b0478 = true := by decide +kernel

theorem c0479 : checkCell pa19 (cellAt 479) b0479 = true := by decide +kernel

theorem c0480 : checkCell pa19 (cellAt 480) b0480 = true := by decide +kernel

theorem c0481 : checkCell pa19 (cellAt 481) b0481 = true := by decide +kernel

theorem c0482 : checkCell pa19 (cellAt 482) b0482 = true := by decide +kernel

theorem c0483 : checkCell pa19 (cellAt 483) b0483 = true := by decide +kernel

theorem c0484 : checkCell pa19 (cellAt 484) b0484 = true := by decide +kernel

theorem slice0475 : slice 475 10 = [cellAt 475, cellAt 476, cellAt 477, cellAt 478, cellAt 479, cellAt 480, cellAt 481, cellAt 482, cellAt 483, cellAt 484] := by decide +kernel

theorem batch0475_ok : checkAll pa19 (slice 475 10) breaks0475 = true := by
  rw [slice0475]
  simp only [breaks0475, checkAll, c0475, c0476, c0477, c0478, c0479, c0480, c0481, c0482, c0483, c0484, Bool.and_self]

theorem batch0475 : ∀ c ∈ slice 475 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0475_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0475
