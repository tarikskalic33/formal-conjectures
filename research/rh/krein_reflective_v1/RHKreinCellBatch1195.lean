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

/-! Serialized cells 1195 to 1204: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1195 : List ℚ := [10275/512]
def b1196 : List ℚ := [82275/4096]
def b1197 : List ℚ := [41175/2048]
def b1198 : List ℚ := [82425/4096]
def b1199 : List ℚ := [20625/1024]
def b1200 : List ℚ := [82575/4096]
def b1201 : List ℚ := [41325/2048]
def b1202 : List ℚ := [82725/4096]
def b1203 : List ℚ := [5175/256]
def b1204 : List ℚ := [41475/2048]

def breaks1195 : List (List ℚ) := [b1195, b1196, b1197, b1198, b1199, b1200, b1201, b1202, b1203, b1204]

theorem c1195 : checkCell pa19 (cellAt 1195) b1195 = true := by decide +kernel

theorem c1196 : checkCell pa19 (cellAt 1196) b1196 = true := by decide +kernel

theorem c1197 : checkCell pa19 (cellAt 1197) b1197 = true := by decide +kernel

theorem c1198 : checkCell pa19 (cellAt 1198) b1198 = true := by decide +kernel

theorem c1199 : checkCell pa19 (cellAt 1199) b1199 = true := by decide +kernel

theorem c1200 : checkCell pa19 (cellAt 1200) b1200 = true := by decide +kernel

theorem c1201 : checkCell pa19 (cellAt 1201) b1201 = true := by decide +kernel

theorem c1202 : checkCell pa19 (cellAt 1202) b1202 = true := by decide +kernel

theorem c1203 : checkCell pa19 (cellAt 1203) b1203 = true := by decide +kernel

theorem c1204 : checkCell pa19 (cellAt 1204) b1204 = true := by decide +kernel

theorem slice1195 : slice 1195 10 = [cellAt 1195, cellAt 1196, cellAt 1197, cellAt 1198, cellAt 1199, cellAt 1200, cellAt 1201, cellAt 1202, cellAt 1203, cellAt 1204] := by decide +kernel

theorem batch1195_ok : checkAll pa19 (slice 1195 10) breaks1195 = true := by
  rw [slice1195]
  simp only [breaks1195, checkAll, c1195, c1196, c1197, c1198, c1199, c1200, c1201, c1202, c1203, c1204, Bool.and_self]

theorem batch1195 : ∀ c ∈ slice 1195 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1195_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1195
