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

/-! Serialized cells 205 to 214: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0205 : List ℚ := [16875/32768]
def b0206 : List ℚ := [8475/16384]
def b0207 : List ℚ := [17025/32768]
def b0208 : List ℚ := [4275/8192]
def b0209 : List ℚ := [17175/32768]
def b0210 : List ℚ := [8625/16384]
def b0211 : List ℚ := [17325/32768]
def b0212 : List ℚ := [2175/4096]
def b0213 : List ℚ := [17475/32768]
def b0214 : List ℚ := [8775/16384]

def breaks0205 : List (List ℚ) := [b0205, b0206, b0207, b0208, b0209, b0210, b0211, b0212, b0213, b0214]

theorem c0205 : checkCell pa19 (cellAt 205) b0205 = true := by decide +kernel

theorem c0206 : checkCell pa19 (cellAt 206) b0206 = true := by decide +kernel

theorem c0207 : checkCell pa19 (cellAt 207) b0207 = true := by decide +kernel

theorem c0208 : checkCell pa19 (cellAt 208) b0208 = true := by decide +kernel

theorem c0209 : checkCell pa19 (cellAt 209) b0209 = true := by decide +kernel

theorem c0210 : checkCell pa19 (cellAt 210) b0210 = true := by decide +kernel

theorem c0211 : checkCell pa19 (cellAt 211) b0211 = true := by decide +kernel

theorem c0212 : checkCell pa19 (cellAt 212) b0212 = true := by decide +kernel

theorem c0213 : checkCell pa19 (cellAt 213) b0213 = true := by decide +kernel

theorem c0214 : checkCell pa19 (cellAt 214) b0214 = true := by decide +kernel

theorem slice0205 : slice 205 10 = [cellAt 205, cellAt 206, cellAt 207, cellAt 208, cellAt 209, cellAt 210, cellAt 211, cellAt 212, cellAt 213, cellAt 214] := by decide +kernel

theorem batch0205_ok : checkAll pa19 (slice 205 10) breaks0205 = true := by
  rw [slice0205]
  simp only [breaks0205, checkAll, c0205, c0206, c0207, c0208, c0209, c0210, c0211, c0212, c0213, c0214, Bool.and_self]

theorem batch0205 : ∀ c ∈ slice 205 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0205_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0205
