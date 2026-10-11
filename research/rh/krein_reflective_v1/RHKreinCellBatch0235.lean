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

/-! Serialized cells 235 to 244: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0235 : List ℚ := [19125/32768]
def b0236 : List ℚ := [75/128]
def b0237 : List ℚ := [19275/32768]
def b0238 : List ℚ := [9675/16384]
def b0239 : List ℚ := [19425/32768]
def b0240 : List ℚ := [4875/8192]
def b0241 : List ℚ := [19575/32768]
def b0242 : List ℚ := [9825/16384]
def b0243 : List ℚ := [19725/32768]
def b0244 : List ℚ := [2475/4096]

def breaks0235 : List (List ℚ) := [b0235, b0236, b0237, b0238, b0239, b0240, b0241, b0242, b0243, b0244]

theorem c0235 : checkCell pa19 (cellAt 235) b0235 = true := by decide +kernel

theorem c0236 : checkCell pa19 (cellAt 236) b0236 = true := by decide +kernel

theorem c0237 : checkCell pa19 (cellAt 237) b0237 = true := by decide +kernel

theorem c0238 : checkCell pa19 (cellAt 238) b0238 = true := by decide +kernel

theorem c0239 : checkCell pa19 (cellAt 239) b0239 = true := by decide +kernel

theorem c0240 : checkCell pa19 (cellAt 240) b0240 = true := by decide +kernel

theorem c0241 : checkCell pa19 (cellAt 241) b0241 = true := by decide +kernel

theorem c0242 : checkCell pa19 (cellAt 242) b0242 = true := by decide +kernel

theorem c0243 : checkCell pa19 (cellAt 243) b0243 = true := by decide +kernel

theorem c0244 : checkCell pa19 (cellAt 244) b0244 = true := by decide +kernel

theorem slice0235 : slice 235 10 = [cellAt 235, cellAt 236, cellAt 237, cellAt 238, cellAt 239, cellAt 240, cellAt 241, cellAt 242, cellAt 243, cellAt 244] := by decide +kernel

theorem batch0235_ok : checkAll pa19 (slice 235 10) breaks0235 = true := by
  rw [slice0235]
  simp only [breaks0235, checkAll, c0235, c0236, c0237, c0238, c0239, c0240, c0241, c0242, c0243, c0244, Bool.and_self]

theorem batch0235 : ∀ c ∈ slice 235 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0235_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0235
