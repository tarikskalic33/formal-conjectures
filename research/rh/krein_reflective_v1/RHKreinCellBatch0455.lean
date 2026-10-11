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

/-! Serialized cells 455 to 464: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0455 : List ℚ := [35625/32768]
def b0456 : List ℚ := [8925/8192]
def b0457 : List ℚ := [35775/32768]
def b0458 : List ℚ := [17925/16384]
def b0459 : List ℚ := [35925/32768]
def b0460 : List ℚ := [1125/1024]
def b0461 : List ℚ := [36075/32768]
def b0462 : List ℚ := [18075/16384]
def b0463 : List ℚ := [36225/32768]
def b0464 : List ℚ := [9075/8192]

def breaks0455 : List (List ℚ) := [b0455, b0456, b0457, b0458, b0459, b0460, b0461, b0462, b0463, b0464]

theorem c0455 : checkCell pa19 (cellAt 455) b0455 = true := by decide +kernel

theorem c0456 : checkCell pa19 (cellAt 456) b0456 = true := by decide +kernel

theorem c0457 : checkCell pa19 (cellAt 457) b0457 = true := by decide +kernel

theorem c0458 : checkCell pa19 (cellAt 458) b0458 = true := by decide +kernel

theorem c0459 : checkCell pa19 (cellAt 459) b0459 = true := by decide +kernel

theorem c0460 : checkCell pa19 (cellAt 460) b0460 = true := by decide +kernel

theorem c0461 : checkCell pa19 (cellAt 461) b0461 = true := by decide +kernel

theorem c0462 : checkCell pa19 (cellAt 462) b0462 = true := by decide +kernel

theorem c0463 : checkCell pa19 (cellAt 463) b0463 = true := by decide +kernel

theorem c0464 : checkCell pa19 (cellAt 464) b0464 = true := by decide +kernel

theorem slice0455 : slice 455 10 = [cellAt 455, cellAt 456, cellAt 457, cellAt 458, cellAt 459, cellAt 460, cellAt 461, cellAt 462, cellAt 463, cellAt 464] := by decide +kernel

theorem batch0455_ok : checkAll pa19 (slice 455 10) breaks0455 = true := by
  rw [slice0455]
  simp only [breaks0455, checkAll, c0455, c0456, c0457, c0458, c0459, c0460, c0461, c0462, c0463, c0464, Bool.and_self]

theorem batch0455 : ∀ c ∈ slice 455 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0455_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0455
