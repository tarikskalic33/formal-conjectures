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

/-! Serialized cells 1325 to 1334: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1325 : List ℚ := [11325/256]
def b1326 : List ℚ := [1425/32]
def b1327 : List ℚ := [11475/256]
def b1328 : List ℚ := [5775/128]
def b1329 : List ℚ := [11625/256]
def b1330 : List ℚ := [2925/64]
def b1331 : List ℚ := [11775/256]
def b1332 : List ℚ := [5925/128]
def b1333 : List ℚ := [11925/256]
def b1334 : List ℚ := [375/8]

def breaks1325 : List (List ℚ) := [b1325, b1326, b1327, b1328, b1329, b1330, b1331, b1332, b1333, b1334]

theorem c1325 : checkCell pa19 (cellAt 1325) b1325 = true := by decide +kernel

theorem c1326 : checkCell pa19 (cellAt 1326) b1326 = true := by decide +kernel

theorem c1327 : checkCell pa19 (cellAt 1327) b1327 = true := by decide +kernel

theorem c1328 : checkCell pa19 (cellAt 1328) b1328 = true := by decide +kernel

theorem c1329 : checkCell pa19 (cellAt 1329) b1329 = true := by decide +kernel

theorem c1330 : checkCell pa19 (cellAt 1330) b1330 = true := by decide +kernel

theorem c1331 : checkCell pa19 (cellAt 1331) b1331 = true := by decide +kernel

theorem c1332 : checkCell pa19 (cellAt 1332) b1332 = true := by decide +kernel

theorem c1333 : checkCell pa19 (cellAt 1333) b1333 = true := by decide +kernel

theorem c1334 : checkCell pa19 (cellAt 1334) b1334 = true := by decide +kernel

theorem slice1325 : slice 1325 10 = [cellAt 1325, cellAt 1326, cellAt 1327, cellAt 1328, cellAt 1329, cellAt 1330, cellAt 1331, cellAt 1332, cellAt 1333, cellAt 1334] := by decide +kernel

theorem batch1325_ok : checkAll pa19 (slice 1325 10) breaks1325 = true := by
  rw [slice1325]
  simp only [breaks1325, checkAll, c1325, c1326, c1327, c1328, c1329, c1330, c1331, c1332, c1333, c1334, Bool.and_self]

theorem batch1325 : ∀ c ∈ slice 1325 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1325_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1325
