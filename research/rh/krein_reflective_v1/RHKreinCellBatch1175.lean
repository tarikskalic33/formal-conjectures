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

/-! Serialized cells 1175 to 1184: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1175 : List ℚ := [20175/1024]
def b1176 : List ℚ := [80775/4096]
def b1177 : List ℚ := [40425/2048]
def b1178 : List ℚ := [80925/4096]
def b1179 : List ℚ := [10125/512]
def b1180 : List ℚ := [81075/4096]
def b1181 : List ℚ := [40575/2048]
def b1182 : List ℚ := [81225/4096]
def b1183 : List ℚ := [20325/1024]
def b1184 : List ℚ := [81375/4096]

def breaks1175 : List (List ℚ) := [b1175, b1176, b1177, b1178, b1179, b1180, b1181, b1182, b1183, b1184]

theorem c1175 : checkCell pa19 (cellAt 1175) b1175 = true := by decide +kernel

theorem c1176 : checkCell pa19 (cellAt 1176) b1176 = true := by decide +kernel

theorem c1177 : checkCell pa19 (cellAt 1177) b1177 = true := by decide +kernel

theorem c1178 : checkCell pa19 (cellAt 1178) b1178 = true := by decide +kernel

theorem c1179 : checkCell pa19 (cellAt 1179) b1179 = true := by decide +kernel

theorem c1180 : checkCell pa19 (cellAt 1180) b1180 = true := by decide +kernel

theorem c1181 : checkCell pa19 (cellAt 1181) b1181 = true := by decide +kernel

theorem c1182 : checkCell pa19 (cellAt 1182) b1182 = true := by decide +kernel

theorem c1183 : checkCell pa19 (cellAt 1183) b1183 = true := by decide +kernel

theorem c1184 : checkCell pa19 (cellAt 1184) b1184 = true := by decide +kernel

theorem slice1175 : slice 1175 10 = [cellAt 1175, cellAt 1176, cellAt 1177, cellAt 1178, cellAt 1179, cellAt 1180, cellAt 1181, cellAt 1182, cellAt 1183, cellAt 1184] := by decide +kernel

theorem batch1175_ok : checkAll pa19 (slice 1175 10) breaks1175 = true := by
  rw [slice1175]
  simp only [breaks1175, checkAll, c1175, c1176, c1177, c1178, c1179, c1180, c1181, c1182, c1183, c1184, Bool.and_self]

theorem batch1175 : ∀ c ∈ slice 1175 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1175_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1175
