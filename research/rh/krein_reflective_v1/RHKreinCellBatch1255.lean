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

/-! Serialized cells 1255 to 1264: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1255 : List ℚ := [28725/1024]
def b1256 : List ℚ := [57525/2048]
def b1257 : List ℚ := [225/8]
def b1258 : List ℚ := [57675/2048]
def b1259 : List ℚ := [28875/1024]
def b1260 : List ℚ := [14475/512]
def b1261 : List ℚ := [29025/1024]
def b1262 : List ℚ := [7275/256]
def b1263 : List ℚ := [14625/512, 3675/128]
def b1264 : List ℚ := [14775/512, 7425/256]

def breaks1255 : List (List ℚ) := [b1255, b1256, b1257, b1258, b1259, b1260, b1261, b1262, b1263, b1264]

theorem c1255 : checkCell pa19 (cellAt 1255) b1255 = true := by decide +kernel

theorem c1256 : checkCell pa19 (cellAt 1256) b1256 = true := by decide +kernel

theorem c1257 : checkCell pa19 (cellAt 1257) b1257 = true := by decide +kernel

theorem c1258 : checkCell pa19 (cellAt 1258) b1258 = true := by decide +kernel

theorem c1259 : checkCell pa19 (cellAt 1259) b1259 = true := by decide +kernel

theorem c1260 : checkCell pa19 (cellAt 1260) b1260 = true := by decide +kernel

theorem c1261 : checkCell pa19 (cellAt 1261) b1261 = true := by decide +kernel

theorem c1262 : checkCell pa19 (cellAt 1262) b1262 = true := by decide +kernel

theorem c1263 : checkCell pa19 (cellAt 1263) b1263 = true := by decide +kernel

theorem c1264 : checkCell pa19 (cellAt 1264) b1264 = true := by decide +kernel

theorem slice1255 : slice 1255 10 = [cellAt 1255, cellAt 1256, cellAt 1257, cellAt 1258, cellAt 1259, cellAt 1260, cellAt 1261, cellAt 1262, cellAt 1263, cellAt 1264] := by decide +kernel

theorem batch1255_ok : checkAll pa19 (slice 1255 10) breaks1255 = true := by
  rw [slice1255]
  simp only [breaks1255, checkAll, c1255, c1256, c1257, c1258, c1259, c1260, c1261, c1262, c1263, c1264, Bool.and_self]

theorem batch1255 : ∀ c ∈ slice 1255 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1255_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1255
