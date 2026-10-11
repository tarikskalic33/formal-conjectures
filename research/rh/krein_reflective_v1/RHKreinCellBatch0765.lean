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

/-! Serialized cells 765 to 774: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0765 : List ℚ := [3375/1024]
def b0766 : List ℚ := [13575/4096]
def b0767 : List ℚ := [6825/2048]
def b0768 : List ℚ := [1725/512]
def b0769 : List ℚ := [6975/2048]
def b0770 : List ℚ := [3525/1024]
def b0771 : List ℚ := [7125/2048]
def b0772 : List ℚ := [14325/4096]
def b0773 : List ℚ := [225/64]
def b0774 : List ℚ := [14475/4096]

def breaks0765 : List (List ℚ) := [b0765, b0766, b0767, b0768, b0769, b0770, b0771, b0772, b0773, b0774]

theorem c0765 : checkCell pa19 (cellAt 765) b0765 = true := by decide +kernel

theorem c0766 : checkCell pa19 (cellAt 766) b0766 = true := by decide +kernel

theorem c0767 : checkCell pa19 (cellAt 767) b0767 = true := by decide +kernel

theorem c0768 : checkCell pa19 (cellAt 768) b0768 = true := by decide +kernel

theorem c0769 : checkCell pa19 (cellAt 769) b0769 = true := by decide +kernel

theorem c0770 : checkCell pa19 (cellAt 770) b0770 = true := by decide +kernel

theorem c0771 : checkCell pa19 (cellAt 771) b0771 = true := by decide +kernel

theorem c0772 : checkCell pa19 (cellAt 772) b0772 = true := by decide +kernel

theorem c0773 : checkCell pa19 (cellAt 773) b0773 = true := by decide +kernel

theorem c0774 : checkCell pa19 (cellAt 774) b0774 = true := by decide +kernel

theorem slice0765 : slice 765 10 = [cellAt 765, cellAt 766, cellAt 767, cellAt 768, cellAt 769, cellAt 770, cellAt 771, cellAt 772, cellAt 773, cellAt 774] := by decide +kernel

theorem batch0765_ok : checkAll pa19 (slice 765 10) breaks0765 = true := by
  rw [slice0765]
  simp only [breaks0765, checkAll, c0765, c0766, c0767, c0768, c0769, c0770, c0771, c0772, c0773, c0774, Bool.and_self]

theorem batch0765 : ∀ c ∈ slice 765 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0765_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0765
