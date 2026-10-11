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

/-! Serialized cells 55 to 64: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0055 : List ℚ := [5625/32768]
def b0056 : List ℚ := [1425/8192]
def b0057 : List ℚ := [5775/32768]
def b0058 : List ℚ := [2925/16384]
def b0059 : List ℚ := [5925/32768]
def b0060 : List ℚ := [375/2048]
def b0061 : List ℚ := [6075/32768]
def b0062 : List ℚ := [3075/16384]
def b0063 : List ℚ := [6225/32768]
def b0064 : List ℚ := [1575/8192]

def breaks0055 : List (List ℚ) := [b0055, b0056, b0057, b0058, b0059, b0060, b0061, b0062, b0063, b0064]

theorem c0055 : checkCell pa19 (cellAt 55) b0055 = true := by decide +kernel

theorem c0056 : checkCell pa19 (cellAt 56) b0056 = true := by decide +kernel

theorem c0057 : checkCell pa19 (cellAt 57) b0057 = true := by decide +kernel

theorem c0058 : checkCell pa19 (cellAt 58) b0058 = true := by decide +kernel

theorem c0059 : checkCell pa19 (cellAt 59) b0059 = true := by decide +kernel

theorem c0060 : checkCell pa19 (cellAt 60) b0060 = true := by decide +kernel

theorem c0061 : checkCell pa19 (cellAt 61) b0061 = true := by decide +kernel

theorem c0062 : checkCell pa19 (cellAt 62) b0062 = true := by decide +kernel

theorem c0063 : checkCell pa19 (cellAt 63) b0063 = true := by decide +kernel

theorem c0064 : checkCell pa19 (cellAt 64) b0064 = true := by decide +kernel

theorem slice0055 : slice 55 10 = [cellAt 55, cellAt 56, cellAt 57, cellAt 58, cellAt 59, cellAt 60, cellAt 61, cellAt 62, cellAt 63, cellAt 64] := by decide +kernel

theorem batch0055_ok : checkAll pa19 (slice 55 10) breaks0055 = true := by
  rw [slice0055]
  simp only [breaks0055, checkAll, c0055, c0056, c0057, c0058, c0059, c0060, c0061, c0062, c0063, c0064, Bool.and_self]

theorem batch0055 : ∀ c ∈ slice 55 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0055_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0055
