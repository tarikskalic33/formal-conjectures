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

/-! Serialized cells 2025 to 2034: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b2025 : List ℚ := [63825/256]
def b2026 : List ℚ := [15975/64]
def b2027 : List ℚ := [63975/256]
def b2028 : List ℚ := [32025/128]
def b2029 : List ℚ := [64125/256]
def b2030 : List ℚ := [8025/32]
def b2031 : List ℚ := [64275/256]
def b2032 : List ℚ := [32175/128]
def b2033 : List ℚ := [64425/256]
def b2034 : List ℚ := [16125/64]

def breaks2025 : List (List ℚ) := [b2025, b2026, b2027, b2028, b2029, b2030, b2031, b2032, b2033, b2034]

theorem c2025 : checkCell pa19 (cellAt 2025) b2025 = true := by decide +kernel

theorem c2026 : checkCell pa19 (cellAt 2026) b2026 = true := by decide +kernel

theorem c2027 : checkCell pa19 (cellAt 2027) b2027 = true := by decide +kernel

theorem c2028 : checkCell pa19 (cellAt 2028) b2028 = true := by decide +kernel

theorem c2029 : checkCell pa19 (cellAt 2029) b2029 = true := by decide +kernel

theorem c2030 : checkCell pa19 (cellAt 2030) b2030 = true := by decide +kernel

theorem c2031 : checkCell pa19 (cellAt 2031) b2031 = true := by decide +kernel

theorem c2032 : checkCell pa19 (cellAt 2032) b2032 = true := by decide +kernel

theorem c2033 : checkCell pa19 (cellAt 2033) b2033 = true := by decide +kernel

theorem c2034 : checkCell pa19 (cellAt 2034) b2034 = true := by decide +kernel

theorem slice2025 : slice 2025 10 = [cellAt 2025, cellAt 2026, cellAt 2027, cellAt 2028, cellAt 2029, cellAt 2030, cellAt 2031, cellAt 2032, cellAt 2033, cellAt 2034] := by decide +kernel

theorem batch2025_ok : checkAll pa19 (slice 2025 10) breaks2025 = true := by
  rw [slice2025]
  simp only [breaks2025, checkAll, c2025, c2026, c2027, c2028, c2029, c2030, c2031, c2032, c2033, c2034, Bool.and_self]

theorem batch2025 : ∀ c ∈ slice 2025 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch2025_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch2025
