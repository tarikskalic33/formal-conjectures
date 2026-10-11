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

/-! Serialized cells 435 to 444: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0435 : List ℚ := [34125/32768]
def b0436 : List ℚ := [4275/4096]
def b0437 : List ℚ := [34275/32768]
def b0438 : List ℚ := [17175/16384]
def b0439 : List ℚ := [34425/32768]
def b0440 : List ℚ := [8625/8192]
def b0441 : List ℚ := [34575/32768]
def b0442 : List ℚ := [17325/16384]
def b0443 : List ℚ := [34725/32768]
def b0444 : List ℚ := [2175/2048]

def breaks0435 : List (List ℚ) := [b0435, b0436, b0437, b0438, b0439, b0440, b0441, b0442, b0443, b0444]

theorem c0435 : checkCell pa19 (cellAt 435) b0435 = true := by decide +kernel

theorem c0436 : checkCell pa19 (cellAt 436) b0436 = true := by decide +kernel

theorem c0437 : checkCell pa19 (cellAt 437) b0437 = true := by decide +kernel

theorem c0438 : checkCell pa19 (cellAt 438) b0438 = true := by decide +kernel

theorem c0439 : checkCell pa19 (cellAt 439) b0439 = true := by decide +kernel

theorem c0440 : checkCell pa19 (cellAt 440) b0440 = true := by decide +kernel

theorem c0441 : checkCell pa19 (cellAt 441) b0441 = true := by decide +kernel

theorem c0442 : checkCell pa19 (cellAt 442) b0442 = true := by decide +kernel

theorem c0443 : checkCell pa19 (cellAt 443) b0443 = true := by decide +kernel

theorem c0444 : checkCell pa19 (cellAt 444) b0444 = true := by decide +kernel

theorem slice0435 : slice 435 10 = [cellAt 435, cellAt 436, cellAt 437, cellAt 438, cellAt 439, cellAt 440, cellAt 441, cellAt 442, cellAt 443, cellAt 444] := by decide +kernel

theorem batch0435_ok : checkAll pa19 (slice 435 10) breaks0435 = true := by
  rw [slice0435]
  simp only [breaks0435, checkAll, c0435, c0436, c0437, c0438, c0439, c0440, c0441, c0442, c0443, c0444, Bool.and_self]

theorem batch0435 : ∀ c ∈ slice 435 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0435_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0435
