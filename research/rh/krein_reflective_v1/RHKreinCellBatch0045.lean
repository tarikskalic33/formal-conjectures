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

/-! Serialized cells 45 to 54: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0045 : List ℚ := [4875/32768]
def b0046 : List ℚ := [2475/16384]
def b0047 : List ℚ := [5025/32768]
def b0048 : List ℚ := [1275/8192]
def b0049 : List ℚ := [5175/32768]
def b0050 : List ℚ := [2625/16384]
def b0051 : List ℚ := [5325/32768]
def b0052 : List ℚ := [675/4096]
def b0053 : List ℚ := [5475/32768]
def b0054 : List ℚ := [2775/16384]

def breaks0045 : List (List ℚ) := [b0045, b0046, b0047, b0048, b0049, b0050, b0051, b0052, b0053, b0054]

theorem c0045 : checkCell pa19 (cellAt 45) b0045 = true := by decide +kernel

theorem c0046 : checkCell pa19 (cellAt 46) b0046 = true := by decide +kernel

theorem c0047 : checkCell pa19 (cellAt 47) b0047 = true := by decide +kernel

theorem c0048 : checkCell pa19 (cellAt 48) b0048 = true := by decide +kernel

theorem c0049 : checkCell pa19 (cellAt 49) b0049 = true := by decide +kernel

theorem c0050 : checkCell pa19 (cellAt 50) b0050 = true := by decide +kernel

theorem c0051 : checkCell pa19 (cellAt 51) b0051 = true := by decide +kernel

theorem c0052 : checkCell pa19 (cellAt 52) b0052 = true := by decide +kernel

theorem c0053 : checkCell pa19 (cellAt 53) b0053 = true := by decide +kernel

theorem c0054 : checkCell pa19 (cellAt 54) b0054 = true := by decide +kernel

theorem slice0045 : slice 45 10 = [cellAt 45, cellAt 46, cellAt 47, cellAt 48, cellAt 49, cellAt 50, cellAt 51, cellAt 52, cellAt 53, cellAt 54] := by decide +kernel

theorem batch0045_ok : checkAll pa19 (slice 45 10) breaks0045 = true := by
  rw [slice0045]
  simp only [breaks0045, checkAll, c0045, c0046, c0047, c0048, c0049, c0050, c0051, c0052, c0053, c0054, Bool.and_self]

theorem batch0045 : ∀ c ∈ slice 45 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0045_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0045
