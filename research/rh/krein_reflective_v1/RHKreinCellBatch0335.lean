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

/-! Serialized cells 335 to 344: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0335 : List ℚ := [26625/32768]
def b0336 : List ℚ := [6675/8192]
def b0337 : List ℚ := [26775/32768]
def b0338 : List ℚ := [13425/16384]
def b0339 : List ℚ := [26925/32768]
def b0340 : List ℚ := [3375/4096]
def b0341 : List ℚ := [27075/32768]
def b0342 : List ℚ := [13575/16384]
def b0343 : List ℚ := [27225/32768]
def b0344 : List ℚ := [6825/8192]

def breaks0335 : List (List ℚ) := [b0335, b0336, b0337, b0338, b0339, b0340, b0341, b0342, b0343, b0344]

theorem c0335 : checkCell pa19 (cellAt 335) b0335 = true := by decide +kernel

theorem c0336 : checkCell pa19 (cellAt 336) b0336 = true := by decide +kernel

theorem c0337 : checkCell pa19 (cellAt 337) b0337 = true := by decide +kernel

theorem c0338 : checkCell pa19 (cellAt 338) b0338 = true := by decide +kernel

theorem c0339 : checkCell pa19 (cellAt 339) b0339 = true := by decide +kernel

theorem c0340 : checkCell pa19 (cellAt 340) b0340 = true := by decide +kernel

theorem c0341 : checkCell pa19 (cellAt 341) b0341 = true := by decide +kernel

theorem c0342 : checkCell pa19 (cellAt 342) b0342 = true := by decide +kernel

theorem c0343 : checkCell pa19 (cellAt 343) b0343 = true := by decide +kernel

theorem c0344 : checkCell pa19 (cellAt 344) b0344 = true := by decide +kernel

theorem slice0335 : slice 335 10 = [cellAt 335, cellAt 336, cellAt 337, cellAt 338, cellAt 339, cellAt 340, cellAt 341, cellAt 342, cellAt 343, cellAt 344] := by decide +kernel

theorem batch0335_ok : checkAll pa19 (slice 335 10) breaks0335 = true := by
  rw [slice0335]
  simp only [breaks0335, checkAll, c0335, c0336, c0337, c0338, c0339, c0340, c0341, c0342, c0343, c0344, Bool.and_self]

theorem batch0335 : ∀ c ∈ slice 335 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0335_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0335
