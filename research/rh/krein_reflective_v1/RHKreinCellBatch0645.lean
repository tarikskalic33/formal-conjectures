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

/-! Serialized cells 645 to 654: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0645 : List ℚ := [29325/16384]
def b0646 : List ℚ := [3675/2048]
def b0647 : List ℚ := [29475/16384]
def b0648 : List ℚ := [14775/8192]
def b0649 : List ℚ := [29625/16384]
def b0650 : List ℚ := [7425/4096]
def b0651 : List ℚ := [29775/16384]
def b0652 : List ℚ := [14925/8192]
def b0653 : List ℚ := [29925/16384]
def b0654 : List ℚ := [1875/1024]

def breaks0645 : List (List ℚ) := [b0645, b0646, b0647, b0648, b0649, b0650, b0651, b0652, b0653, b0654]

theorem c0645 : checkCell pa19 (cellAt 645) b0645 = true := by decide +kernel

theorem c0646 : checkCell pa19 (cellAt 646) b0646 = true := by decide +kernel

theorem c0647 : checkCell pa19 (cellAt 647) b0647 = true := by decide +kernel

theorem c0648 : checkCell pa19 (cellAt 648) b0648 = true := by decide +kernel

theorem c0649 : checkCell pa19 (cellAt 649) b0649 = true := by decide +kernel

theorem c0650 : checkCell pa19 (cellAt 650) b0650 = true := by decide +kernel

theorem c0651 : checkCell pa19 (cellAt 651) b0651 = true := by decide +kernel

theorem c0652 : checkCell pa19 (cellAt 652) b0652 = true := by decide +kernel

theorem c0653 : checkCell pa19 (cellAt 653) b0653 = true := by decide +kernel

theorem c0654 : checkCell pa19 (cellAt 654) b0654 = true := by decide +kernel

theorem slice0645 : slice 645 10 = [cellAt 645, cellAt 646, cellAt 647, cellAt 648, cellAt 649, cellAt 650, cellAt 651, cellAt 652, cellAt 653, cellAt 654] := by decide +kernel

theorem batch0645_ok : checkAll pa19 (slice 645 10) breaks0645 = true := by
  rw [slice0645]
  simp only [breaks0645, checkAll, c0645, c0646, c0647, c0648, c0649, c0650, c0651, c0652, c0653, c0654, Bool.and_self]

theorem batch0645 : ∀ c ∈ slice 645 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0645_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0645
