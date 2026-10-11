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

/-! Serialized cells 315 to 324: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0315 : List ℚ := [25125/32768]
def b0316 : List ℚ := [1575/2048]
def b0317 : List ℚ := [25275/32768]
def b0318 : List ℚ := [12675/16384]
def b0319 : List ℚ := [25425/32768]
def b0320 : List ℚ := [6375/8192]
def b0321 : List ℚ := [25575/32768]
def b0322 : List ℚ := [12825/16384]
def b0323 : List ℚ := [25725/32768]
def b0324 : List ℚ := [3225/4096]

def breaks0315 : List (List ℚ) := [b0315, b0316, b0317, b0318, b0319, b0320, b0321, b0322, b0323, b0324]

theorem c0315 : checkCell pa19 (cellAt 315) b0315 = true := by decide +kernel

theorem c0316 : checkCell pa19 (cellAt 316) b0316 = true := by decide +kernel

theorem c0317 : checkCell pa19 (cellAt 317) b0317 = true := by decide +kernel

theorem c0318 : checkCell pa19 (cellAt 318) b0318 = true := by decide +kernel

theorem c0319 : checkCell pa19 (cellAt 319) b0319 = true := by decide +kernel

theorem c0320 : checkCell pa19 (cellAt 320) b0320 = true := by decide +kernel

theorem c0321 : checkCell pa19 (cellAt 321) b0321 = true := by decide +kernel

theorem c0322 : checkCell pa19 (cellAt 322) b0322 = true := by decide +kernel

theorem c0323 : checkCell pa19 (cellAt 323) b0323 = true := by decide +kernel

theorem c0324 : checkCell pa19 (cellAt 324) b0324 = true := by decide +kernel

theorem slice0315 : slice 315 10 = [cellAt 315, cellAt 316, cellAt 317, cellAt 318, cellAt 319, cellAt 320, cellAt 321, cellAt 322, cellAt 323, cellAt 324] := by decide +kernel

theorem batch0315_ok : checkAll pa19 (slice 315 10) breaks0315 = true := by
  rw [slice0315]
  simp only [breaks0315, checkAll, c0315, c0316, c0317, c0318, c0319, c0320, c0321, c0322, c0323, c0324, Bool.and_self]

theorem batch0315 : ∀ c ∈ slice 315 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0315_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0315
