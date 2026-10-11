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

/-! Serialized cells 685 to 694: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0685 : List ℚ := [17175/8192]
def b0686 : List ℚ := [8625/4096]
def b0687 : List ℚ := [17325/8192]
def b0688 : List ℚ := [2175/1024]
def b0689 : List ℚ := [17475/8192]
def b0690 : List ℚ := [8775/4096]
def b0691 : List ℚ := [17625/8192]
def b0692 : List ℚ := [4425/2048]
def b0693 : List ℚ := [17775/8192]
def b0694 : List ℚ := [8925/4096]

def breaks0685 : List (List ℚ) := [b0685, b0686, b0687, b0688, b0689, b0690, b0691, b0692, b0693, b0694]

theorem c0685 : checkCell pa19 (cellAt 685) b0685 = true := by decide +kernel

theorem c0686 : checkCell pa19 (cellAt 686) b0686 = true := by decide +kernel

theorem c0687 : checkCell pa19 (cellAt 687) b0687 = true := by decide +kernel

theorem c0688 : checkCell pa19 (cellAt 688) b0688 = true := by decide +kernel

theorem c0689 : checkCell pa19 (cellAt 689) b0689 = true := by decide +kernel

theorem c0690 : checkCell pa19 (cellAt 690) b0690 = true := by decide +kernel

theorem c0691 : checkCell pa19 (cellAt 691) b0691 = true := by decide +kernel

theorem c0692 : checkCell pa19 (cellAt 692) b0692 = true := by decide +kernel

theorem c0693 : checkCell pa19 (cellAt 693) b0693 = true := by decide +kernel

theorem c0694 : checkCell pa19 (cellAt 694) b0694 = true := by decide +kernel

theorem slice0685 : slice 685 10 = [cellAt 685, cellAt 686, cellAt 687, cellAt 688, cellAt 689, cellAt 690, cellAt 691, cellAt 692, cellAt 693, cellAt 694] := by decide +kernel

theorem batch0685_ok : checkAll pa19 (slice 685 10) breaks0685 = true := by
  rw [slice0685]
  simp only [breaks0685, checkAll, c0685, c0686, c0687, c0688, c0689, c0690, c0691, c0692, c0693, c0694, Bool.and_self]

theorem batch0685 : ∀ c ∈ slice 685 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0685_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0685
