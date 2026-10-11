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

/-! Serialized cells 605 to 614: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0605 : List ℚ := [26325/16384]
def b0606 : List ℚ := [825/512]
def b0607 : List ℚ := [26475/16384]
def b0608 : List ℚ := [13275/8192]
def b0609 : List ℚ := [26625/16384]
def b0610 : List ℚ := [6675/4096]
def b0611 : List ℚ := [26775/16384]
def b0612 : List ℚ := [13425/8192]
def b0613 : List ℚ := [26925/16384]
def b0614 : List ℚ := [3375/2048]

def breaks0605 : List (List ℚ) := [b0605, b0606, b0607, b0608, b0609, b0610, b0611, b0612, b0613, b0614]

theorem c0605 : checkCell pa19 (cellAt 605) b0605 = true := by decide +kernel

theorem c0606 : checkCell pa19 (cellAt 606) b0606 = true := by decide +kernel

theorem c0607 : checkCell pa19 (cellAt 607) b0607 = true := by decide +kernel

theorem c0608 : checkCell pa19 (cellAt 608) b0608 = true := by decide +kernel

theorem c0609 : checkCell pa19 (cellAt 609) b0609 = true := by decide +kernel

theorem c0610 : checkCell pa19 (cellAt 610) b0610 = true := by decide +kernel

theorem c0611 : checkCell pa19 (cellAt 611) b0611 = true := by decide +kernel

theorem c0612 : checkCell pa19 (cellAt 612) b0612 = true := by decide +kernel

theorem c0613 : checkCell pa19 (cellAt 613) b0613 = true := by decide +kernel

theorem c0614 : checkCell pa19 (cellAt 614) b0614 = true := by decide +kernel

theorem slice0605 : slice 605 10 = [cellAt 605, cellAt 606, cellAt 607, cellAt 608, cellAt 609, cellAt 610, cellAt 611, cellAt 612, cellAt 613, cellAt 614] := by decide +kernel

theorem batch0605_ok : checkAll pa19 (slice 605 10) breaks0605 = true := by
  rw [slice0605]
  simp only [breaks0605, checkAll, c0605, c0606, c0607, c0608, c0609, c0610, c0611, c0612, c0613, c0614, Bool.and_self]

theorem batch0605 : ∀ c ∈ slice 605 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0605_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0605
