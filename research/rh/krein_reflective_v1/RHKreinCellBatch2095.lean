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

/-! Serialized cells 2095 to 2104: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b2095 : List ℚ := [69075/256]
def b2096 : List ℚ := [34575/128]
def b2097 : List ℚ := [69225/256]
def b2098 : List ℚ := [17325/64]
def b2099 : List ℚ := [69375/256]
def b2100 : List ℚ := [34725/128]
def b2101 : List ℚ := [69525/256]
def b2102 : List ℚ := [2175/8]
def b2103 : List ℚ := [69675/256]
def b2104 : List ℚ := [34875/128]

def breaks2095 : List (List ℚ) := [b2095, b2096, b2097, b2098, b2099, b2100, b2101, b2102, b2103, b2104]

theorem c2095 : checkCell pa19 (cellAt 2095) b2095 = true := by decide +kernel

theorem c2096 : checkCell pa19 (cellAt 2096) b2096 = true := by decide +kernel

theorem c2097 : checkCell pa19 (cellAt 2097) b2097 = true := by decide +kernel

theorem c2098 : checkCell pa19 (cellAt 2098) b2098 = true := by decide +kernel

theorem c2099 : checkCell pa19 (cellAt 2099) b2099 = true := by decide +kernel

theorem c2100 : checkCell pa19 (cellAt 2100) b2100 = true := by decide +kernel

theorem c2101 : checkCell pa19 (cellAt 2101) b2101 = true := by decide +kernel

theorem c2102 : checkCell pa19 (cellAt 2102) b2102 = true := by decide +kernel

theorem c2103 : checkCell pa19 (cellAt 2103) b2103 = true := by decide +kernel

theorem c2104 : checkCell pa19 (cellAt 2104) b2104 = true := by decide +kernel

theorem slice2095 : slice 2095 10 = [cellAt 2095, cellAt 2096, cellAt 2097, cellAt 2098, cellAt 2099, cellAt 2100, cellAt 2101, cellAt 2102, cellAt 2103, cellAt 2104] := by decide +kernel

theorem batch2095_ok : checkAll pa19 (slice 2095 10) breaks2095 = true := by
  rw [slice2095]
  simp only [breaks2095, checkAll, c2095, c2096, c2097, c2098, c2099, c2100, c2101, c2102, c2103, c2104, Bool.and_self]

theorem batch2095 : ∀ c ∈ slice 2095 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch2095_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch2095
