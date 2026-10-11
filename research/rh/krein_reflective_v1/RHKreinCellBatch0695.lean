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

/-! Serialized cells 695 to 704: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0695 : List ℚ := [17925/8192]
def b0696 : List ℚ := [1125/512]
def b0697 : List ℚ := [18075/8192]
def b0698 : List ℚ := [9075/4096]
def b0699 : List ℚ := [18225/8192]
def b0700 : List ℚ := [4575/2048]
def b0701 : List ℚ := [18375/8192]
def b0702 : List ℚ := [9225/4096]
def b0703 : List ℚ := [18525/8192]
def b0704 : List ℚ := [2325/1024]

def breaks0695 : List (List ℚ) := [b0695, b0696, b0697, b0698, b0699, b0700, b0701, b0702, b0703, b0704]

theorem c0695 : checkCell pa19 (cellAt 695) b0695 = true := by decide +kernel

theorem c0696 : checkCell pa19 (cellAt 696) b0696 = true := by decide +kernel

theorem c0697 : checkCell pa19 (cellAt 697) b0697 = true := by decide +kernel

theorem c0698 : checkCell pa19 (cellAt 698) b0698 = true := by decide +kernel

theorem c0699 : checkCell pa19 (cellAt 699) b0699 = true := by decide +kernel

theorem c0700 : checkCell pa19 (cellAt 700) b0700 = true := by decide +kernel

theorem c0701 : checkCell pa19 (cellAt 701) b0701 = true := by decide +kernel

theorem c0702 : checkCell pa19 (cellAt 702) b0702 = true := by decide +kernel

theorem c0703 : checkCell pa19 (cellAt 703) b0703 = true := by decide +kernel

theorem c0704 : checkCell pa19 (cellAt 704) b0704 = true := by decide +kernel

theorem slice0695 : slice 695 10 = [cellAt 695, cellAt 696, cellAt 697, cellAt 698, cellAt 699, cellAt 700, cellAt 701, cellAt 702, cellAt 703, cellAt 704] := by decide +kernel

theorem batch0695_ok : checkAll pa19 (slice 695 10) breaks0695 = true := by
  rw [slice0695]
  simp only [breaks0695, checkAll, c0695, c0696, c0697, c0698, c0699, c0700, c0701, c0702, c0703, c0704, Bool.and_self]

theorem batch0695 : ∀ c ∈ slice 695 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0695_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0695
