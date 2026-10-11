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

/-! Serialized cells 1225 to 1234: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1225 : List ℚ := [3225/128]
def b1226 : List ℚ := [6525/256]
def b1227 : List ℚ := [825/32]
def b1228 : List ℚ := [6675/256]
def b1229 : List ℚ := [13425/512]
def b1230 : List ℚ := [26925/1024]
def b1231 : List ℚ := [3375/128]
def b1232 : List ℚ := [54075/2048]
def b1233 : List ℚ := [27075/1024]
def b1234 : List ℚ := [13575/512]

def breaks1225 : List (List ℚ) := [b1225, b1226, b1227, b1228, b1229, b1230, b1231, b1232, b1233, b1234]

theorem c1225 : checkCell pa19 (cellAt 1225) b1225 = true := by decide +kernel

theorem c1226 : checkCell pa19 (cellAt 1226) b1226 = true := by decide +kernel

theorem c1227 : checkCell pa19 (cellAt 1227) b1227 = true := by decide +kernel

theorem c1228 : checkCell pa19 (cellAt 1228) b1228 = true := by decide +kernel

theorem c1229 : checkCell pa19 (cellAt 1229) b1229 = true := by decide +kernel

theorem c1230 : checkCell pa19 (cellAt 1230) b1230 = true := by decide +kernel

theorem c1231 : checkCell pa19 (cellAt 1231) b1231 = true := by decide +kernel

theorem c1232 : checkCell pa19 (cellAt 1232) b1232 = true := by decide +kernel

theorem c1233 : checkCell pa19 (cellAt 1233) b1233 = true := by decide +kernel

theorem c1234 : checkCell pa19 (cellAt 1234) b1234 = true := by decide +kernel

theorem slice1225 : slice 1225 10 = [cellAt 1225, cellAt 1226, cellAt 1227, cellAt 1228, cellAt 1229, cellAt 1230, cellAt 1231, cellAt 1232, cellAt 1233, cellAt 1234] := by decide +kernel

theorem batch1225_ok : checkAll pa19 (slice 1225 10) breaks1225 = true := by
  rw [slice1225]
  simp only [breaks1225, checkAll, c1225, c1226, c1227, c1228, c1229, c1230, c1231, c1232, c1233, c1234, Bool.and_self]

theorem batch1225 : ∀ c ∈ slice 1225 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1225_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1225
