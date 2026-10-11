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

/-! Serialized cells 1235 to 1244: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1235 : List ℚ := [27225/1024]
def b1236 : List ℚ := [6825/256]
def b1237 : List ℚ := [27375/1024]
def b1238 : List ℚ := [13725/512]
def b1239 : List ℚ := [1725/64]
def b1240 : List ℚ := [13875/512]
def b1241 : List ℚ := [6975/256]
def b1242 : List ℚ := [14025/512]
def b1243 : List ℚ := [28125/1024]
def b1244 : List ℚ := [3525/128]

def breaks1235 : List (List ℚ) := [b1235, b1236, b1237, b1238, b1239, b1240, b1241, b1242, b1243, b1244]

theorem c1235 : checkCell pa19 (cellAt 1235) b1235 = true := by decide +kernel

theorem c1236 : checkCell pa19 (cellAt 1236) b1236 = true := by decide +kernel

theorem c1237 : checkCell pa19 (cellAt 1237) b1237 = true := by decide +kernel

theorem c1238 : checkCell pa19 (cellAt 1238) b1238 = true := by decide +kernel

theorem c1239 : checkCell pa19 (cellAt 1239) b1239 = true := by decide +kernel

theorem c1240 : checkCell pa19 (cellAt 1240) b1240 = true := by decide +kernel

theorem c1241 : checkCell pa19 (cellAt 1241) b1241 = true := by decide +kernel

theorem c1242 : checkCell pa19 (cellAt 1242) b1242 = true := by decide +kernel

theorem c1243 : checkCell pa19 (cellAt 1243) b1243 = true := by decide +kernel

theorem c1244 : checkCell pa19 (cellAt 1244) b1244 = true := by decide +kernel

theorem slice1235 : slice 1235 10 = [cellAt 1235, cellAt 1236, cellAt 1237, cellAt 1238, cellAt 1239, cellAt 1240, cellAt 1241, cellAt 1242, cellAt 1243, cellAt 1244] := by decide +kernel

theorem batch1235_ok : checkAll pa19 (slice 1235 10) breaks1235 = true := by
  rw [slice1235]
  simp only [breaks1235, checkAll, c1235, c1236, c1237, c1238, c1239, c1240, c1241, c1242, c1243, c1244, Bool.and_self]

theorem batch1235 : ∀ c ∈ slice 1235 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1235_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1235
