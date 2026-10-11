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

/-! Serialized cells 1045 to 1054: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1045 : List ℚ := [24225/2048]
def b1046 : List ℚ := [48525/4096]
def b1047 : List ℚ := [6075/512]
def b1048 : List ℚ := [48675/4096]
def b1049 : List ℚ := [24375/2048]
def b1050 : List ℚ := [48825/4096]
def b1051 : List ℚ := [12225/1024]
def b1052 : List ℚ := [48975/4096]
def b1053 : List ℚ := [24525/2048]
def b1054 : List ℚ := [49125/4096]

def breaks1045 : List (List ℚ) := [b1045, b1046, b1047, b1048, b1049, b1050, b1051, b1052, b1053, b1054]

theorem c1045 : checkCell pa19 (cellAt 1045) b1045 = true := by decide +kernel

theorem c1046 : checkCell pa19 (cellAt 1046) b1046 = true := by decide +kernel

theorem c1047 : checkCell pa19 (cellAt 1047) b1047 = true := by decide +kernel

theorem c1048 : checkCell pa19 (cellAt 1048) b1048 = true := by decide +kernel

theorem c1049 : checkCell pa19 (cellAt 1049) b1049 = true := by decide +kernel

theorem c1050 : checkCell pa19 (cellAt 1050) b1050 = true := by decide +kernel

theorem c1051 : checkCell pa19 (cellAt 1051) b1051 = true := by decide +kernel

theorem c1052 : checkCell pa19 (cellAt 1052) b1052 = true := by decide +kernel

theorem c1053 : checkCell pa19 (cellAt 1053) b1053 = true := by decide +kernel

theorem c1054 : checkCell pa19 (cellAt 1054) b1054 = true := by decide +kernel

theorem slice1045 : slice 1045 10 = [cellAt 1045, cellAt 1046, cellAt 1047, cellAt 1048, cellAt 1049, cellAt 1050, cellAt 1051, cellAt 1052, cellAt 1053, cellAt 1054] := by decide +kernel

theorem batch1045_ok : checkAll pa19 (slice 1045 10) breaks1045 = true := by
  rw [slice1045]
  simp only [breaks1045, checkAll, c1045, c1046, c1047, c1048, c1049, c1050, c1051, c1052, c1053, c1054, Bool.and_self]

theorem batch1045 : ∀ c ∈ slice 1045 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1045_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1045
