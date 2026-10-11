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

/-! Serialized cells 1295 to 1304: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1295 : List ℚ := [36825/1024]
def b1296 : List ℚ := [9225/256]
def b1297 : List ℚ := [18525/512]
def b1298 : List ℚ := [2325/64]
def b1299 : List ℚ := [18675/512, 9375/256]
def b1300 : List ℚ := [18825/512, 4725/128]
def b1301 : List ℚ := [18975/512, 9525/256]
def b1302 : List ℚ := [19125/512, 75/2]
def b1303 : List ℚ := [19275/512, 9675/256]
def b1304 : List ℚ := [4875/128]

def breaks1295 : List (List ℚ) := [b1295, b1296, b1297, b1298, b1299, b1300, b1301, b1302, b1303, b1304]

theorem c1295 : checkCell pa19 (cellAt 1295) b1295 = true := by decide +kernel

theorem c1296 : checkCell pa19 (cellAt 1296) b1296 = true := by decide +kernel

theorem c1297 : checkCell pa19 (cellAt 1297) b1297 = true := by decide +kernel

theorem c1298 : checkCell pa19 (cellAt 1298) b1298 = true := by decide +kernel

theorem c1299 : checkCell pa19 (cellAt 1299) b1299 = true := by decide +kernel

theorem c1300 : checkCell pa19 (cellAt 1300) b1300 = true := by decide +kernel

theorem c1301 : checkCell pa19 (cellAt 1301) b1301 = true := by decide +kernel

theorem c1302 : checkCell pa19 (cellAt 1302) b1302 = true := by decide +kernel

theorem c1303 : checkCell pa19 (cellAt 1303) b1303 = true := by decide +kernel

theorem c1304 : checkCell pa19 (cellAt 1304) b1304 = true := by decide +kernel

theorem slice1295 : slice 1295 10 = [cellAt 1295, cellAt 1296, cellAt 1297, cellAt 1298, cellAt 1299, cellAt 1300, cellAt 1301, cellAt 1302, cellAt 1303, cellAt 1304] := by decide +kernel

theorem batch1295_ok : checkAll pa19 (slice 1295 10) breaks1295 = true := by
  rw [slice1295]
  simp only [breaks1295, checkAll, c1295, c1296, c1297, c1298, c1299, c1300, c1301, c1302, c1303, c1304, Bool.and_self]

theorem batch1295 : ∀ c ∈ slice 1295 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1295_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1295
