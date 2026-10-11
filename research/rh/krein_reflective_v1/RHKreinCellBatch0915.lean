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

/-! Serialized cells 915 to 924: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0915 : List ℚ := [15675/2048]
def b0916 : List ℚ := [7875/1024]
def b0917 : List ℚ := [15825/2048]
def b0918 : List ℚ := [3975/512]
def b0919 : List ℚ := [15975/2048]
def b0920 : List ℚ := [8025/1024]
def b0921 : List ℚ := [16125/2048]
def b0922 : List ℚ := [2025/256]
def b0923 : List ℚ := [16275/2048]
def b0924 : List ℚ := [8175/1024]

def breaks0915 : List (List ℚ) := [b0915, b0916, b0917, b0918, b0919, b0920, b0921, b0922, b0923, b0924]

theorem c0915 : checkCell pa19 (cellAt 915) b0915 = true := by decide +kernel

theorem c0916 : checkCell pa19 (cellAt 916) b0916 = true := by decide +kernel

theorem c0917 : checkCell pa19 (cellAt 917) b0917 = true := by decide +kernel

theorem c0918 : checkCell pa19 (cellAt 918) b0918 = true := by decide +kernel

theorem c0919 : checkCell pa19 (cellAt 919) b0919 = true := by decide +kernel

theorem c0920 : checkCell pa19 (cellAt 920) b0920 = true := by decide +kernel

theorem c0921 : checkCell pa19 (cellAt 921) b0921 = true := by decide +kernel

theorem c0922 : checkCell pa19 (cellAt 922) b0922 = true := by decide +kernel

theorem c0923 : checkCell pa19 (cellAt 923) b0923 = true := by decide +kernel

theorem c0924 : checkCell pa19 (cellAt 924) b0924 = true := by decide +kernel

theorem slice0915 : slice 915 10 = [cellAt 915, cellAt 916, cellAt 917, cellAt 918, cellAt 919, cellAt 920, cellAt 921, cellAt 922, cellAt 923, cellAt 924] := by decide +kernel

theorem batch0915_ok : checkAll pa19 (slice 915 10) breaks0915 = true := by
  rw [slice0915]
  simp only [breaks0915, checkAll, c0915, c0916, c0917, c0918, c0919, c0920, c0921, c0922, c0923, c0924, Bool.and_self]

theorem batch0915 : ∀ c ∈ slice 915 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0915_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0915
