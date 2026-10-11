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

/-! Serialized cells 275 to 284: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0275 : List ℚ := [22125/32768]
def b0276 : List ℚ := [2775/4096]
def b0277 : List ℚ := [22275/32768]
def b0278 : List ℚ := [11175/16384]
def b0279 : List ℚ := [22425/32768]
def b0280 : List ℚ := [5625/8192]
def b0281 : List ℚ := [22575/32768]
def b0282 : List ℚ := [11325/16384]
def b0283 : List ℚ := [22725/32768]
def b0284 : List ℚ := [1425/2048]

def breaks0275 : List (List ℚ) := [b0275, b0276, b0277, b0278, b0279, b0280, b0281, b0282, b0283, b0284]

theorem c0275 : checkCell pa19 (cellAt 275) b0275 = true := by decide +kernel

theorem c0276 : checkCell pa19 (cellAt 276) b0276 = true := by decide +kernel

theorem c0277 : checkCell pa19 (cellAt 277) b0277 = true := by decide +kernel

theorem c0278 : checkCell pa19 (cellAt 278) b0278 = true := by decide +kernel

theorem c0279 : checkCell pa19 (cellAt 279) b0279 = true := by decide +kernel

theorem c0280 : checkCell pa19 (cellAt 280) b0280 = true := by decide +kernel

theorem c0281 : checkCell pa19 (cellAt 281) b0281 = true := by decide +kernel

theorem c0282 : checkCell pa19 (cellAt 282) b0282 = true := by decide +kernel

theorem c0283 : checkCell pa19 (cellAt 283) b0283 = true := by decide +kernel

theorem c0284 : checkCell pa19 (cellAt 284) b0284 = true := by decide +kernel

theorem slice0275 : slice 275 10 = [cellAt 275, cellAt 276, cellAt 277, cellAt 278, cellAt 279, cellAt 280, cellAt 281, cellAt 282, cellAt 283, cellAt 284] := by decide +kernel

theorem batch0275_ok : checkAll pa19 (slice 275 10) breaks0275 = true := by
  rw [slice0275]
  simp only [breaks0275, checkAll, c0275, c0276, c0277, c0278, c0279, c0280, c0281, c0282, c0283, c0284, Bool.and_self]

theorem batch0275 : ∀ c ∈ slice 275 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0275_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0275
