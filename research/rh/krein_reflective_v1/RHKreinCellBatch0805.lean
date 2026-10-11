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

/-! Serialized cells 805 to 814: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0805 : List ℚ := [525/128]
def b0806 : List ℚ := [16875/4096]
def b0807 : List ℚ := [8475/2048]
def b0808 : List ℚ := [17025/4096]
def b0809 : List ℚ := [4275/1024]
def b0810 : List ℚ := [17175/4096]
def b0811 : List ℚ := [8625/2048]
def b0812 : List ℚ := [17325/4096]
def b0813 : List ℚ := [2175/512]
def b0814 : List ℚ := [17475/4096]

def breaks0805 : List (List ℚ) := [b0805, b0806, b0807, b0808, b0809, b0810, b0811, b0812, b0813, b0814]

theorem c0805 : checkCell pa19 (cellAt 805) b0805 = true := by decide +kernel

theorem c0806 : checkCell pa19 (cellAt 806) b0806 = true := by decide +kernel

theorem c0807 : checkCell pa19 (cellAt 807) b0807 = true := by decide +kernel

theorem c0808 : checkCell pa19 (cellAt 808) b0808 = true := by decide +kernel

theorem c0809 : checkCell pa19 (cellAt 809) b0809 = true := by decide +kernel

theorem c0810 : checkCell pa19 (cellAt 810) b0810 = true := by decide +kernel

theorem c0811 : checkCell pa19 (cellAt 811) b0811 = true := by decide +kernel

theorem c0812 : checkCell pa19 (cellAt 812) b0812 = true := by decide +kernel

theorem c0813 : checkCell pa19 (cellAt 813) b0813 = true := by decide +kernel

theorem c0814 : checkCell pa19 (cellAt 814) b0814 = true := by decide +kernel

theorem slice0805 : slice 805 10 = [cellAt 805, cellAt 806, cellAt 807, cellAt 808, cellAt 809, cellAt 810, cellAt 811, cellAt 812, cellAt 813, cellAt 814] := by decide +kernel

theorem batch0805_ok : checkAll pa19 (slice 805 10) breaks0805 = true := by
  rw [slice0805]
  simp only [breaks0805, checkAll, c0805, c0806, c0807, c0808, c0809, c0810, c0811, c0812, c0813, c0814, Bool.and_self]

theorem batch0805 : ∀ c ∈ slice 805 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0805_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0805
