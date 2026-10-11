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

/-! Serialized cells 1055 to 1064: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1055 : List ℚ := [3075/256]
def b1056 : List ℚ := [49275/4096]
def b1057 : List ℚ := [24675/2048]
def b1058 : List ℚ := [49425/4096]
def b1059 : List ℚ := [12375/1024]
def b1060 : List ℚ := [49575/4096]
def b1061 : List ℚ := [24825/2048]
def b1062 : List ℚ := [49725/4096]
def b1063 : List ℚ := [6225/512]
def b1064 : List ℚ := [49875/4096]

def breaks1055 : List (List ℚ) := [b1055, b1056, b1057, b1058, b1059, b1060, b1061, b1062, b1063, b1064]

theorem c1055 : checkCell pa19 (cellAt 1055) b1055 = true := by decide +kernel

theorem c1056 : checkCell pa19 (cellAt 1056) b1056 = true := by decide +kernel

theorem c1057 : checkCell pa19 (cellAt 1057) b1057 = true := by decide +kernel

theorem c1058 : checkCell pa19 (cellAt 1058) b1058 = true := by decide +kernel

theorem c1059 : checkCell pa19 (cellAt 1059) b1059 = true := by decide +kernel

theorem c1060 : checkCell pa19 (cellAt 1060) b1060 = true := by decide +kernel

theorem c1061 : checkCell pa19 (cellAt 1061) b1061 = true := by decide +kernel

theorem c1062 : checkCell pa19 (cellAt 1062) b1062 = true := by decide +kernel

theorem c1063 : checkCell pa19 (cellAt 1063) b1063 = true := by decide +kernel

theorem c1064 : checkCell pa19 (cellAt 1064) b1064 = true := by decide +kernel

theorem slice1055 : slice 1055 10 = [cellAt 1055, cellAt 1056, cellAt 1057, cellAt 1058, cellAt 1059, cellAt 1060, cellAt 1061, cellAt 1062, cellAt 1063, cellAt 1064] := by decide +kernel

theorem batch1055_ok : checkAll pa19 (slice 1055 10) breaks1055 = true := by
  rw [slice1055]
  simp only [breaks1055, checkAll, c1055, c1056, c1057, c1058, c1059, c1060, c1061, c1062, c1063, c1064, Bool.and_self]

theorem batch1055 : ∀ c ∈ slice 1055 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1055_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1055
