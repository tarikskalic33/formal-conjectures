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

/-! Serialized cells 365 to 374: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0365 : List ℚ := [28875/32768]
def b0366 : List ℚ := [14475/16384]
def b0367 : List ℚ := [29025/32768]
def b0368 : List ℚ := [7275/8192]
def b0369 : List ℚ := [29175/32768]
def b0370 : List ℚ := [14625/16384]
def b0371 : List ℚ := [29325/32768]
def b0372 : List ℚ := [3675/4096]
def b0373 : List ℚ := [29475/32768]
def b0374 : List ℚ := [14775/16384]

def breaks0365 : List (List ℚ) := [b0365, b0366, b0367, b0368, b0369, b0370, b0371, b0372, b0373, b0374]

theorem c0365 : checkCell pa19 (cellAt 365) b0365 = true := by decide +kernel

theorem c0366 : checkCell pa19 (cellAt 366) b0366 = true := by decide +kernel

theorem c0367 : checkCell pa19 (cellAt 367) b0367 = true := by decide +kernel

theorem c0368 : checkCell pa19 (cellAt 368) b0368 = true := by decide +kernel

theorem c0369 : checkCell pa19 (cellAt 369) b0369 = true := by decide +kernel

theorem c0370 : checkCell pa19 (cellAt 370) b0370 = true := by decide +kernel

theorem c0371 : checkCell pa19 (cellAt 371) b0371 = true := by decide +kernel

theorem c0372 : checkCell pa19 (cellAt 372) b0372 = true := by decide +kernel

theorem c0373 : checkCell pa19 (cellAt 373) b0373 = true := by decide +kernel

theorem c0374 : checkCell pa19 (cellAt 374) b0374 = true := by decide +kernel

theorem slice0365 : slice 365 10 = [cellAt 365, cellAt 366, cellAt 367, cellAt 368, cellAt 369, cellAt 370, cellAt 371, cellAt 372, cellAt 373, cellAt 374] := by decide +kernel

theorem batch0365_ok : checkAll pa19 (slice 365 10) breaks0365 = true := by
  rw [slice0365]
  simp only [breaks0365, checkAll, c0365, c0366, c0367, c0368, c0369, c0370, c0371, c0372, c0373, c0374, Bool.and_self]

theorem batch0365 : ∀ c ∈ slice 365 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0365_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0365
