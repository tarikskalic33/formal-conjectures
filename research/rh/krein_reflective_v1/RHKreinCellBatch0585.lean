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

/-! Serialized cells 585 to 594: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0585 : List ℚ := [24825/16384]
def b0586 : List ℚ := [6225/4096]
def b0587 : List ℚ := [24975/16384]
def b0588 : List ℚ := [12525/8192]
def b0589 : List ℚ := [25125/16384]
def b0590 : List ℚ := [1575/1024]
def b0591 : List ℚ := [25275/16384]
def b0592 : List ℚ := [12675/8192]
def b0593 : List ℚ := [25425/16384]
def b0594 : List ℚ := [6375/4096]

def breaks0585 : List (List ℚ) := [b0585, b0586, b0587, b0588, b0589, b0590, b0591, b0592, b0593, b0594]

theorem c0585 : checkCell pa19 (cellAt 585) b0585 = true := by decide +kernel

theorem c0586 : checkCell pa19 (cellAt 586) b0586 = true := by decide +kernel

theorem c0587 : checkCell pa19 (cellAt 587) b0587 = true := by decide +kernel

theorem c0588 : checkCell pa19 (cellAt 588) b0588 = true := by decide +kernel

theorem c0589 : checkCell pa19 (cellAt 589) b0589 = true := by decide +kernel

theorem c0590 : checkCell pa19 (cellAt 590) b0590 = true := by decide +kernel

theorem c0591 : checkCell pa19 (cellAt 591) b0591 = true := by decide +kernel

theorem c0592 : checkCell pa19 (cellAt 592) b0592 = true := by decide +kernel

theorem c0593 : checkCell pa19 (cellAt 593) b0593 = true := by decide +kernel

theorem c0594 : checkCell pa19 (cellAt 594) b0594 = true := by decide +kernel

theorem slice0585 : slice 585 10 = [cellAt 585, cellAt 586, cellAt 587, cellAt 588, cellAt 589, cellAt 590, cellAt 591, cellAt 592, cellAt 593, cellAt 594] := by decide +kernel

theorem batch0585_ok : checkAll pa19 (slice 585 10) breaks0585 = true := by
  rw [slice0585]
  simp only [breaks0585, checkAll, c0585, c0586, c0587, c0588, c0589, c0590, c0591, c0592, c0593, c0594, Bool.and_self]

theorem batch0585 : ∀ c ∈ slice 585 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0585_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0585
