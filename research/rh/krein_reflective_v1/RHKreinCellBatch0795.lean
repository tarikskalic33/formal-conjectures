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

/-! Serialized cells 795 to 804: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0795 : List ℚ := [8025/2048]
def b0796 : List ℚ := [16125/4096]
def b0797 : List ℚ := [2025/512]
def b0798 : List ℚ := [16275/4096]
def b0799 : List ℚ := [8175/2048]
def b0800 : List ℚ := [16425/4096]
def b0801 : List ℚ := [4125/1024]
def b0802 : List ℚ := [16575/4096]
def b0803 : List ℚ := [8325/2048]
def b0804 : List ℚ := [16725/4096]

def breaks0795 : List (List ℚ) := [b0795, b0796, b0797, b0798, b0799, b0800, b0801, b0802, b0803, b0804]

theorem c0795 : checkCell pa19 (cellAt 795) b0795 = true := by decide +kernel

theorem c0796 : checkCell pa19 (cellAt 796) b0796 = true := by decide +kernel

theorem c0797 : checkCell pa19 (cellAt 797) b0797 = true := by decide +kernel

theorem c0798 : checkCell pa19 (cellAt 798) b0798 = true := by decide +kernel

theorem c0799 : checkCell pa19 (cellAt 799) b0799 = true := by decide +kernel

theorem c0800 : checkCell pa19 (cellAt 800) b0800 = true := by decide +kernel

theorem c0801 : checkCell pa19 (cellAt 801) b0801 = true := by decide +kernel

theorem c0802 : checkCell pa19 (cellAt 802) b0802 = true := by decide +kernel

theorem c0803 : checkCell pa19 (cellAt 803) b0803 = true := by decide +kernel

theorem c0804 : checkCell pa19 (cellAt 804) b0804 = true := by decide +kernel

theorem slice0795 : slice 795 10 = [cellAt 795, cellAt 796, cellAt 797, cellAt 798, cellAt 799, cellAt 800, cellAt 801, cellAt 802, cellAt 803, cellAt 804] := by decide +kernel

theorem batch0795_ok : checkAll pa19 (slice 795 10) breaks0795 = true := by
  rw [slice0795]
  simp only [breaks0795, checkAll, c0795, c0796, c0797, c0798, c0799, c0800, c0801, c0802, c0803, c0804, Bool.and_self]

theorem batch0795 : ∀ c ∈ slice 795 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0795_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0795
