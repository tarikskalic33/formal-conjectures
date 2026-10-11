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

/-! Serialized cells 2035 to 2044: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b2035 : List ℚ := [64575/256]
def b2036 : List ℚ := [32325/128]
def b2037 : List ℚ := [64725/256]
def b2038 : List ℚ := [2025/8]
def b2039 : List ℚ := [64875/256]
def b2040 : List ℚ := [32475/128]
def b2041 : List ℚ := [129975/512, 65025/256]
def b2042 : List ℚ := [130125/512, 16275/64]
def b2043 : List ℚ := [130275/512, 65175/256]
def b2044 : List ℚ := [130425/512, 32625/128]

def breaks2035 : List (List ℚ) := [b2035, b2036, b2037, b2038, b2039, b2040, b2041, b2042, b2043, b2044]

theorem c2035 : checkCell pa19 (cellAt 2035) b2035 = true := by decide +kernel

theorem c2036 : checkCell pa19 (cellAt 2036) b2036 = true := by decide +kernel

theorem c2037 : checkCell pa19 (cellAt 2037) b2037 = true := by decide +kernel

theorem c2038 : checkCell pa19 (cellAt 2038) b2038 = true := by decide +kernel

theorem c2039 : checkCell pa19 (cellAt 2039) b2039 = true := by decide +kernel

theorem c2040 : checkCell pa19 (cellAt 2040) b2040 = true := by decide +kernel

theorem c2041 : checkCell pa19 (cellAt 2041) b2041 = true := by decide +kernel

theorem c2042 : checkCell pa19 (cellAt 2042) b2042 = true := by decide +kernel

theorem c2043 : checkCell pa19 (cellAt 2043) b2043 = true := by decide +kernel

theorem c2044 : checkCell pa19 (cellAt 2044) b2044 = true := by decide +kernel

theorem slice2035 : slice 2035 10 = [cellAt 2035, cellAt 2036, cellAt 2037, cellAt 2038, cellAt 2039, cellAt 2040, cellAt 2041, cellAt 2042, cellAt 2043, cellAt 2044] := by decide +kernel

theorem batch2035_ok : checkAll pa19 (slice 2035 10) breaks2035 = true := by
  rw [slice2035]
  simp only [breaks2035, checkAll, c2035, c2036, c2037, c2038, c2039, c2040, c2041, c2042, c2043, c2044, Bool.and_self]

theorem batch2035 : ∀ c ∈ slice 2035 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch2035_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch2035
