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

/-! Serialized cells 705 to 714: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0705 : List ℚ := [18675/8192]
def b0706 : List ℚ := [9375/4096]
def b0707 : List ℚ := [18825/8192]
def b0708 : List ℚ := [4725/2048]
def b0709 : List ℚ := [18975/8192]
def b0710 : List ℚ := [9525/4096]
def b0711 : List ℚ := [19125/8192]
def b0712 : List ℚ := [75/32]
def b0713 : List ℚ := [19275/8192]
def b0714 : List ℚ := [9675/4096]

def breaks0705 : List (List ℚ) := [b0705, b0706, b0707, b0708, b0709, b0710, b0711, b0712, b0713, b0714]

theorem c0705 : checkCell pa19 (cellAt 705) b0705 = true := by decide +kernel

theorem c0706 : checkCell pa19 (cellAt 706) b0706 = true := by decide +kernel

theorem c0707 : checkCell pa19 (cellAt 707) b0707 = true := by decide +kernel

theorem c0708 : checkCell pa19 (cellAt 708) b0708 = true := by decide +kernel

theorem c0709 : checkCell pa19 (cellAt 709) b0709 = true := by decide +kernel

theorem c0710 : checkCell pa19 (cellAt 710) b0710 = true := by decide +kernel

theorem c0711 : checkCell pa19 (cellAt 711) b0711 = true := by decide +kernel

theorem c0712 : checkCell pa19 (cellAt 712) b0712 = true := by decide +kernel

theorem c0713 : checkCell pa19 (cellAt 713) b0713 = true := by decide +kernel

theorem c0714 : checkCell pa19 (cellAt 714) b0714 = true := by decide +kernel

theorem slice0705 : slice 705 10 = [cellAt 705, cellAt 706, cellAt 707, cellAt 708, cellAt 709, cellAt 710, cellAt 711, cellAt 712, cellAt 713, cellAt 714] := by decide +kernel

theorem batch0705_ok : checkAll pa19 (slice 705 10) breaks0705 = true := by
  rw [slice0705]
  simp only [breaks0705, checkAll, c0705, c0706, c0707, c0708, c0709, c0710, c0711, c0712, c0713, c0714, Bool.and_self]

theorem batch0705 : ∀ c ∈ slice 705 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0705_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0705
