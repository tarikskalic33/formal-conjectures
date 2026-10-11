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

/-! Serialized cells 775 to 784: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0775 : List ℚ := [7275/2048]
def b0776 : List ℚ := [14625/4096]
def b0777 : List ℚ := [3675/1024]
def b0778 : List ℚ := [14775/4096]
def b0779 : List ℚ := [7425/2048]
def b0780 : List ℚ := [14925/4096]
def b0781 : List ℚ := [1875/512]
def b0782 : List ℚ := [15075/4096]
def b0783 : List ℚ := [7575/2048]
def b0784 : List ℚ := [15225/4096]

def breaks0775 : List (List ℚ) := [b0775, b0776, b0777, b0778, b0779, b0780, b0781, b0782, b0783, b0784]

theorem c0775 : checkCell pa19 (cellAt 775) b0775 = true := by decide +kernel

theorem c0776 : checkCell pa19 (cellAt 776) b0776 = true := by decide +kernel

theorem c0777 : checkCell pa19 (cellAt 777) b0777 = true := by decide +kernel

theorem c0778 : checkCell pa19 (cellAt 778) b0778 = true := by decide +kernel

theorem c0779 : checkCell pa19 (cellAt 779) b0779 = true := by decide +kernel

theorem c0780 : checkCell pa19 (cellAt 780) b0780 = true := by decide +kernel

theorem c0781 : checkCell pa19 (cellAt 781) b0781 = true := by decide +kernel

theorem c0782 : checkCell pa19 (cellAt 782) b0782 = true := by decide +kernel

theorem c0783 : checkCell pa19 (cellAt 783) b0783 = true := by decide +kernel

theorem c0784 : checkCell pa19 (cellAt 784) b0784 = true := by decide +kernel

theorem slice0775 : slice 775 10 = [cellAt 775, cellAt 776, cellAt 777, cellAt 778, cellAt 779, cellAt 780, cellAt 781, cellAt 782, cellAt 783, cellAt 784] := by decide +kernel

theorem batch0775_ok : checkAll pa19 (slice 775 10) breaks0775 = true := by
  rw [slice0775]
  simp only [breaks0775, checkAll, c0775, c0776, c0777, c0778, c0779, c0780, c0781, c0782, c0783, c0784, Bool.and_self]

theorem batch0775 : ∀ c ∈ slice 775 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0775_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0775
