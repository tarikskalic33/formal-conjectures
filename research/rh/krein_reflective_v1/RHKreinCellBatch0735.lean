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

/-! Serialized cells 735 to 744: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0735 : List ℚ := [5625/2048]
def b0736 : List ℚ := [11325/4096]
def b0737 : List ℚ := [1425/512]
def b0738 : List ℚ := [11475/4096]
def b0739 : List ℚ := [5775/2048]
def b0740 : List ℚ := [11625/4096]
def b0741 : List ℚ := [2925/1024]
def b0742 : List ℚ := [11775/4096]
def b0743 : List ℚ := [5925/2048]
def b0744 : List ℚ := [11925/4096]

def breaks0735 : List (List ℚ) := [b0735, b0736, b0737, b0738, b0739, b0740, b0741, b0742, b0743, b0744]

theorem c0735 : checkCell pa19 (cellAt 735) b0735 = true := by decide +kernel

theorem c0736 : checkCell pa19 (cellAt 736) b0736 = true := by decide +kernel

theorem c0737 : checkCell pa19 (cellAt 737) b0737 = true := by decide +kernel

theorem c0738 : checkCell pa19 (cellAt 738) b0738 = true := by decide +kernel

theorem c0739 : checkCell pa19 (cellAt 739) b0739 = true := by decide +kernel

theorem c0740 : checkCell pa19 (cellAt 740) b0740 = true := by decide +kernel

theorem c0741 : checkCell pa19 (cellAt 741) b0741 = true := by decide +kernel

theorem c0742 : checkCell pa19 (cellAt 742) b0742 = true := by decide +kernel

theorem c0743 : checkCell pa19 (cellAt 743) b0743 = true := by decide +kernel

theorem c0744 : checkCell pa19 (cellAt 744) b0744 = true := by decide +kernel

theorem slice0735 : slice 735 10 = [cellAt 735, cellAt 736, cellAt 737, cellAt 738, cellAt 739, cellAt 740, cellAt 741, cellAt 742, cellAt 743, cellAt 744] := by decide +kernel

theorem batch0735_ok : checkAll pa19 (slice 735 10) breaks0735 = true := by
  rw [slice0735]
  simp only [breaks0735, checkAll, c0735, c0736, c0737, c0738, c0739, c0740, c0741, c0742, c0743, c0744, Bool.and_self]

theorem batch0735 : ∀ c ∈ slice 735 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0735_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0735
