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

/-! Serialized cells 2075 to 2084: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b2075 : List ℚ := [67575/256]
def b2076 : List ℚ := [33825/128]
def b2077 : List ℚ := [67725/256]
def b2078 : List ℚ := [8475/32]
def b2079 : List ℚ := [67875/256]
def b2080 : List ℚ := [33975/128]
def b2081 : List ℚ := [68025/256]
def b2082 : List ℚ := [17025/64]
def b2083 : List ℚ := [68175/256]
def b2084 : List ℚ := [34125/128]

def breaks2075 : List (List ℚ) := [b2075, b2076, b2077, b2078, b2079, b2080, b2081, b2082, b2083, b2084]

theorem c2075 : checkCell pa19 (cellAt 2075) b2075 = true := by decide +kernel

theorem c2076 : checkCell pa19 (cellAt 2076) b2076 = true := by decide +kernel

theorem c2077 : checkCell pa19 (cellAt 2077) b2077 = true := by decide +kernel

theorem c2078 : checkCell pa19 (cellAt 2078) b2078 = true := by decide +kernel

theorem c2079 : checkCell pa19 (cellAt 2079) b2079 = true := by decide +kernel

theorem c2080 : checkCell pa19 (cellAt 2080) b2080 = true := by decide +kernel

theorem c2081 : checkCell pa19 (cellAt 2081) b2081 = true := by decide +kernel

theorem c2082 : checkCell pa19 (cellAt 2082) b2082 = true := by decide +kernel

theorem c2083 : checkCell pa19 (cellAt 2083) b2083 = true := by decide +kernel

theorem c2084 : checkCell pa19 (cellAt 2084) b2084 = true := by decide +kernel

theorem slice2075 : slice 2075 10 = [cellAt 2075, cellAt 2076, cellAt 2077, cellAt 2078, cellAt 2079, cellAt 2080, cellAt 2081, cellAt 2082, cellAt 2083, cellAt 2084] := by decide +kernel

theorem batch2075_ok : checkAll pa19 (slice 2075 10) breaks2075 = true := by
  rw [slice2075]
  simp only [breaks2075, checkAll, c2075, c2076, c2077, c2078, c2079, c2080, c2081, c2082, c2083, c2084, Bool.and_self]

theorem batch2075 : ∀ c ∈ slice 2075 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch2075_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch2075
