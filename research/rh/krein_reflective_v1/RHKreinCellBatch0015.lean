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

/-! Serialized cells 15 to 24: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0015 : List ℚ := [2625/32768]
def b0016 : List ℚ := [675/8192]
def b0017 : List ℚ := [2775/32768]
def b0018 : List ℚ := [1425/16384]
def b0019 : List ℚ := [2925/32768]
def b0020 : List ℚ := [375/4096]
def b0021 : List ℚ := [3075/32768]
def b0022 : List ℚ := [1575/16384]
def b0023 : List ℚ := [3225/32768]
def b0024 : List ℚ := [825/8192]

def breaks0015 : List (List ℚ) := [b0015, b0016, b0017, b0018, b0019, b0020, b0021, b0022, b0023, b0024]

theorem c0015 : checkCell pa19 (cellAt 15) b0015 = true := by decide +kernel

theorem c0016 : checkCell pa19 (cellAt 16) b0016 = true := by decide +kernel

theorem c0017 : checkCell pa19 (cellAt 17) b0017 = true := by decide +kernel

theorem c0018 : checkCell pa19 (cellAt 18) b0018 = true := by decide +kernel

theorem c0019 : checkCell pa19 (cellAt 19) b0019 = true := by decide +kernel

theorem c0020 : checkCell pa19 (cellAt 20) b0020 = true := by decide +kernel

theorem c0021 : checkCell pa19 (cellAt 21) b0021 = true := by decide +kernel

theorem c0022 : checkCell pa19 (cellAt 22) b0022 = true := by decide +kernel

theorem c0023 : checkCell pa19 (cellAt 23) b0023 = true := by decide +kernel

theorem c0024 : checkCell pa19 (cellAt 24) b0024 = true := by decide +kernel

theorem slice0015 : slice 15 10 = [cellAt 15, cellAt 16, cellAt 17, cellAt 18, cellAt 19, cellAt 20, cellAt 21, cellAt 22, cellAt 23, cellAt 24] := by decide +kernel

theorem batch0015_ok : checkAll pa19 (slice 15 10) breaks0015 = true := by
  rw [slice0015]
  simp only [breaks0015, checkAll, c0015, c0016, c0017, c0018, c0019, c0020, c0021, c0022, c0023, c0024, Bool.and_self]

theorem batch0015 : ∀ c ∈ slice 15 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0015_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0015
