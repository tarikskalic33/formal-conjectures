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

/-! Serialized cells 1205 to 1214: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1205 : List ℚ := [20775/1024]
def b1206 : List ℚ := [41625/2048]
def b1207 : List ℚ := [10425/512]
def b1208 : List ℚ := [20925/1024]
def b1209 : List ℚ := [2625/128]
def b1210 : List ℚ := [10575/512, 5325/256]
def b1211 : List ℚ := [675/32]
def b1212 : List ℚ := [5475/256]
def b1213 : List ℚ := [2775/128]
def b1214 : List ℚ := [5625/256]

def breaks1205 : List (List ℚ) := [b1205, b1206, b1207, b1208, b1209, b1210, b1211, b1212, b1213, b1214]

theorem c1205 : checkCell pa19 (cellAt 1205) b1205 = true := by decide +kernel

theorem c1206 : checkCell pa19 (cellAt 1206) b1206 = true := by decide +kernel

theorem c1207 : checkCell pa19 (cellAt 1207) b1207 = true := by decide +kernel

theorem c1208 : checkCell pa19 (cellAt 1208) b1208 = true := by decide +kernel

theorem c1209 : checkCell pa19 (cellAt 1209) b1209 = true := by decide +kernel

theorem c1210 : checkCell pa19 (cellAt 1210) b1210 = true := by decide +kernel

theorem c1211 : checkCell pa19 (cellAt 1211) b1211 = true := by decide +kernel

theorem c1212 : checkCell pa19 (cellAt 1212) b1212 = true := by decide +kernel

theorem c1213 : checkCell pa19 (cellAt 1213) b1213 = true := by decide +kernel

theorem c1214 : checkCell pa19 (cellAt 1214) b1214 = true := by decide +kernel

theorem slice1205 : slice 1205 10 = [cellAt 1205, cellAt 1206, cellAt 1207, cellAt 1208, cellAt 1209, cellAt 1210, cellAt 1211, cellAt 1212, cellAt 1213, cellAt 1214] := by decide +kernel

theorem batch1205_ok : checkAll pa19 (slice 1205 10) breaks1205 = true := by
  rw [slice1205]
  simp only [breaks1205, checkAll, c1205, c1206, c1207, c1208, c1209, c1210, c1211, c1212, c1213, c1214, Bool.and_self]

theorem batch1205 : ∀ c ∈ slice 1205 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1205_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1205
