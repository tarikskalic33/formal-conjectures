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

/-! Serialized cells 465 to 474: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0465 : List ℚ := [36375/32768]
def b0466 : List ℚ := [18225/16384]
def b0467 : List ℚ := [36525/32768]
def b0468 : List ℚ := [4575/4096]
def b0469 : List ℚ := [36675/32768]
def b0470 : List ℚ := [18375/16384]
def b0471 : List ℚ := [36825/32768]
def b0472 : List ℚ := [9225/8192]
def b0473 : List ℚ := [36975/32768]
def b0474 : List ℚ := [18525/16384]

def breaks0465 : List (List ℚ) := [b0465, b0466, b0467, b0468, b0469, b0470, b0471, b0472, b0473, b0474]

theorem c0465 : checkCell pa19 (cellAt 465) b0465 = true := by decide +kernel

theorem c0466 : checkCell pa19 (cellAt 466) b0466 = true := by decide +kernel

theorem c0467 : checkCell pa19 (cellAt 467) b0467 = true := by decide +kernel

theorem c0468 : checkCell pa19 (cellAt 468) b0468 = true := by decide +kernel

theorem c0469 : checkCell pa19 (cellAt 469) b0469 = true := by decide +kernel

theorem c0470 : checkCell pa19 (cellAt 470) b0470 = true := by decide +kernel

theorem c0471 : checkCell pa19 (cellAt 471) b0471 = true := by decide +kernel

theorem c0472 : checkCell pa19 (cellAt 472) b0472 = true := by decide +kernel

theorem c0473 : checkCell pa19 (cellAt 473) b0473 = true := by decide +kernel

theorem c0474 : checkCell pa19 (cellAt 474) b0474 = true := by decide +kernel

theorem slice0465 : slice 465 10 = [cellAt 465, cellAt 466, cellAt 467, cellAt 468, cellAt 469, cellAt 470, cellAt 471, cellAt 472, cellAt 473, cellAt 474] := by decide +kernel

theorem batch0465_ok : checkAll pa19 (slice 465 10) breaks0465 = true := by
  rw [slice0465]
  simp only [breaks0465, checkAll, c0465, c0466, c0467, c0468, c0469, c0470, c0471, c0472, c0473, c0474, Bool.and_self]

theorem batch0465 : ∀ c ∈ slice 465 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0465_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0465
