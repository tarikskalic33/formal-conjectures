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

/-! Serialized cells 2065 to 2074: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b2065 : List ℚ := [66825/256]
def b2066 : List ℚ := [16725/64]
def b2067 : List ℚ := [66975/256]
def b2068 : List ℚ := [33525/128]
def b2069 : List ℚ := [67125/256]
def b2070 : List ℚ := [525/2]
def b2071 : List ℚ := [67275/256]
def b2072 : List ℚ := [33675/128]
def b2073 : List ℚ := [67425/256]
def b2074 : List ℚ := [16875/64]

def breaks2065 : List (List ℚ) := [b2065, b2066, b2067, b2068, b2069, b2070, b2071, b2072, b2073, b2074]

theorem c2065 : checkCell pa19 (cellAt 2065) b2065 = true := by decide +kernel

theorem c2066 : checkCell pa19 (cellAt 2066) b2066 = true := by decide +kernel

theorem c2067 : checkCell pa19 (cellAt 2067) b2067 = true := by decide +kernel

theorem c2068 : checkCell pa19 (cellAt 2068) b2068 = true := by decide +kernel

theorem c2069 : checkCell pa19 (cellAt 2069) b2069 = true := by decide +kernel

theorem c2070 : checkCell pa19 (cellAt 2070) b2070 = true := by decide +kernel

theorem c2071 : checkCell pa19 (cellAt 2071) b2071 = true := by decide +kernel

theorem c2072 : checkCell pa19 (cellAt 2072) b2072 = true := by decide +kernel

theorem c2073 : checkCell pa19 (cellAt 2073) b2073 = true := by decide +kernel

theorem c2074 : checkCell pa19 (cellAt 2074) b2074 = true := by decide +kernel

theorem slice2065 : slice 2065 10 = [cellAt 2065, cellAt 2066, cellAt 2067, cellAt 2068, cellAt 2069, cellAt 2070, cellAt 2071, cellAt 2072, cellAt 2073, cellAt 2074] := by decide +kernel

theorem batch2065_ok : checkAll pa19 (slice 2065 10) breaks2065 = true := by
  rw [slice2065]
  simp only [breaks2065, checkAll, c2065, c2066, c2067, c2068, c2069, c2070, c2071, c2072, c2073, c2074, Bool.and_self]

theorem batch2065 : ∀ c ∈ slice 2065 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch2065_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch2065
