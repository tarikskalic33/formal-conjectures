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

/-! Serialized cells 1035 to 1044: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1035 : List ℚ := [11925/1024]
def b1036 : List ℚ := [47775/4096]
def b1037 : List ℚ := [23925/2048]
def b1038 : List ℚ := [47925/4096]
def b1039 : List ℚ := [375/32]
def b1040 : List ℚ := [48075/4096]
def b1041 : List ℚ := [24075/2048]
def b1042 : List ℚ := [48225/4096]
def b1043 : List ℚ := [12075/1024]
def b1044 : List ℚ := [48375/4096]

def breaks1035 : List (List ℚ) := [b1035, b1036, b1037, b1038, b1039, b1040, b1041, b1042, b1043, b1044]

theorem c1035 : checkCell pa19 (cellAt 1035) b1035 = true := by decide +kernel

theorem c1036 : checkCell pa19 (cellAt 1036) b1036 = true := by decide +kernel

theorem c1037 : checkCell pa19 (cellAt 1037) b1037 = true := by decide +kernel

theorem c1038 : checkCell pa19 (cellAt 1038) b1038 = true := by decide +kernel

theorem c1039 : checkCell pa19 (cellAt 1039) b1039 = true := by decide +kernel

theorem c1040 : checkCell pa19 (cellAt 1040) b1040 = true := by decide +kernel

theorem c1041 : checkCell pa19 (cellAt 1041) b1041 = true := by decide +kernel

theorem c1042 : checkCell pa19 (cellAt 1042) b1042 = true := by decide +kernel

theorem c1043 : checkCell pa19 (cellAt 1043) b1043 = true := by decide +kernel

theorem c1044 : checkCell pa19 (cellAt 1044) b1044 = true := by decide +kernel

theorem slice1035 : slice 1035 10 = [cellAt 1035, cellAt 1036, cellAt 1037, cellAt 1038, cellAt 1039, cellAt 1040, cellAt 1041, cellAt 1042, cellAt 1043, cellAt 1044] := by decide +kernel

theorem batch1035_ok : checkAll pa19 (slice 1035 10) breaks1035 = true := by
  rw [slice1035]
  simp only [breaks1035, checkAll, c1035, c1036, c1037, c1038, c1039, c1040, c1041, c1042, c1043, c1044, Bool.and_self]

theorem batch1035 : ∀ c ∈ slice 1035 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1035_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1035
