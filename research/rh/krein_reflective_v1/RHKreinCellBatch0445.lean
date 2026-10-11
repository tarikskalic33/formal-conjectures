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

/-! Serialized cells 445 to 454: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0445 : List ℚ := [34875/32768]
def b0446 : List ℚ := [17475/16384]
def b0447 : List ℚ := [35025/32768]
def b0448 : List ℚ := [8775/8192]
def b0449 : List ℚ := [35175/32768]
def b0450 : List ℚ := [17625/16384]
def b0451 : List ℚ := [35325/32768]
def b0452 : List ℚ := [4425/4096]
def b0453 : List ℚ := [35475/32768]
def b0454 : List ℚ := [17775/16384]

def breaks0445 : List (List ℚ) := [b0445, b0446, b0447, b0448, b0449, b0450, b0451, b0452, b0453, b0454]

theorem c0445 : checkCell pa19 (cellAt 445) b0445 = true := by decide +kernel

theorem c0446 : checkCell pa19 (cellAt 446) b0446 = true := by decide +kernel

theorem c0447 : checkCell pa19 (cellAt 447) b0447 = true := by decide +kernel

theorem c0448 : checkCell pa19 (cellAt 448) b0448 = true := by decide +kernel

theorem c0449 : checkCell pa19 (cellAt 449) b0449 = true := by decide +kernel

theorem c0450 : checkCell pa19 (cellAt 450) b0450 = true := by decide +kernel

theorem c0451 : checkCell pa19 (cellAt 451) b0451 = true := by decide +kernel

theorem c0452 : checkCell pa19 (cellAt 452) b0452 = true := by decide +kernel

theorem c0453 : checkCell pa19 (cellAt 453) b0453 = true := by decide +kernel

theorem c0454 : checkCell pa19 (cellAt 454) b0454 = true := by decide +kernel

theorem slice0445 : slice 445 10 = [cellAt 445, cellAt 446, cellAt 447, cellAt 448, cellAt 449, cellAt 450, cellAt 451, cellAt 452, cellAt 453, cellAt 454] := by decide +kernel

theorem batch0445_ok : checkAll pa19 (slice 445 10) breaks0445 = true := by
  rw [slice0445]
  simp only [breaks0445, checkAll, c0445, c0446, c0447, c0448, c0449, c0450, c0451, c0452, c0453, c0454, Bool.and_self]

theorem batch0445 : ∀ c ∈ slice 445 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0445_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0445
