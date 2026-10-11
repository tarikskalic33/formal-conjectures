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

/-! Serialized cells 1275 to 1284: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1275 : List ℚ := [4125/128]
def b1276 : List ℚ := [8325/256]
def b1277 : List ℚ := [525/16]
def b1278 : List ℚ := [8475/256]
def b1279 : List ℚ := [4275/128]
def b1280 : List ℚ := [8625/256]
def b1281 : List ℚ := [2175/64]
def b1282 : List ℚ := [8775/256]
def b1283 : List ℚ := [4425/128]
def b1284 : List ℚ := [8925/256]

def breaks1275 : List (List ℚ) := [b1275, b1276, b1277, b1278, b1279, b1280, b1281, b1282, b1283, b1284]

theorem c1275 : checkCell pa19 (cellAt 1275) b1275 = true := by decide +kernel

theorem c1276 : checkCell pa19 (cellAt 1276) b1276 = true := by decide +kernel

theorem c1277 : checkCell pa19 (cellAt 1277) b1277 = true := by decide +kernel

theorem c1278 : checkCell pa19 (cellAt 1278) b1278 = true := by decide +kernel

theorem c1279 : checkCell pa19 (cellAt 1279) b1279 = true := by decide +kernel

theorem c1280 : checkCell pa19 (cellAt 1280) b1280 = true := by decide +kernel

theorem c1281 : checkCell pa19 (cellAt 1281) b1281 = true := by decide +kernel

theorem c1282 : checkCell pa19 (cellAt 1282) b1282 = true := by decide +kernel

theorem c1283 : checkCell pa19 (cellAt 1283) b1283 = true := by decide +kernel

theorem c1284 : checkCell pa19 (cellAt 1284) b1284 = true := by decide +kernel

theorem slice1275 : slice 1275 10 = [cellAt 1275, cellAt 1276, cellAt 1277, cellAt 1278, cellAt 1279, cellAt 1280, cellAt 1281, cellAt 1282, cellAt 1283, cellAt 1284] := by decide +kernel

theorem batch1275_ok : checkAll pa19 (slice 1275 10) breaks1275 = true := by
  rw [slice1275]
  simp only [breaks1275, checkAll, c1275, c1276, c1277, c1278, c1279, c1280, c1281, c1282, c1283, c1284, Bool.and_self]

theorem batch1275 : ∀ c ∈ slice 1275 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1275_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1275
