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

/-! Serialized cells 1245 to 1254: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1245 : List ℚ := [28275/1024]
def b1246 : List ℚ := [14175/512]
def b1247 : List ℚ := [28425/1024]
def b1248 : List ℚ := [56925/2048]
def b1249 : List ℚ := [7125/256]
def b1250 : List ℚ := [57075/2048]
def b1251 : List ℚ := [28575/1024]
def b1252 : List ℚ := [57225/2048]
def b1253 : List ℚ := [14325/512]
def b1254 : List ℚ := [57375/2048]

def breaks1245 : List (List ℚ) := [b1245, b1246, b1247, b1248, b1249, b1250, b1251, b1252, b1253, b1254]

theorem c1245 : checkCell pa19 (cellAt 1245) b1245 = true := by decide +kernel

theorem c1246 : checkCell pa19 (cellAt 1246) b1246 = true := by decide +kernel

theorem c1247 : checkCell pa19 (cellAt 1247) b1247 = true := by decide +kernel

theorem c1248 : checkCell pa19 (cellAt 1248) b1248 = true := by decide +kernel

theorem c1249 : checkCell pa19 (cellAt 1249) b1249 = true := by decide +kernel

theorem c1250 : checkCell pa19 (cellAt 1250) b1250 = true := by decide +kernel

theorem c1251 : checkCell pa19 (cellAt 1251) b1251 = true := by decide +kernel

theorem c1252 : checkCell pa19 (cellAt 1252) b1252 = true := by decide +kernel

theorem c1253 : checkCell pa19 (cellAt 1253) b1253 = true := by decide +kernel

theorem c1254 : checkCell pa19 (cellAt 1254) b1254 = true := by decide +kernel

theorem slice1245 : slice 1245 10 = [cellAt 1245, cellAt 1246, cellAt 1247, cellAt 1248, cellAt 1249, cellAt 1250, cellAt 1251, cellAt 1252, cellAt 1253, cellAt 1254] := by decide +kernel

theorem batch1245_ok : checkAll pa19 (slice 1245 10) breaks1245 = true := by
  rw [slice1245]
  simp only [breaks1245, checkAll, c1245, c1246, c1247, c1248, c1249, c1250, c1251, c1252, c1253, c1254, Bool.and_self]

theorem batch1245 : ∀ c ∈ slice 1245 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1245_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1245
