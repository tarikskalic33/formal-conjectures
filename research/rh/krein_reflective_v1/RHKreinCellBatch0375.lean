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

/-! Serialized cells 375 to 384: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0375 : List ℚ := [29625/32768]
def b0376 : List ℚ := [7425/8192]
def b0377 : List ℚ := [29775/32768]
def b0378 : List ℚ := [14925/16384]
def b0379 : List ℚ := [29925/32768]
def b0380 : List ℚ := [1875/2048]
def b0381 : List ℚ := [30075/32768]
def b0382 : List ℚ := [15075/16384]
def b0383 : List ℚ := [30225/32768]
def b0384 : List ℚ := [7575/8192]

def breaks0375 : List (List ℚ) := [b0375, b0376, b0377, b0378, b0379, b0380, b0381, b0382, b0383, b0384]

theorem c0375 : checkCell pa19 (cellAt 375) b0375 = true := by decide +kernel

theorem c0376 : checkCell pa19 (cellAt 376) b0376 = true := by decide +kernel

theorem c0377 : checkCell pa19 (cellAt 377) b0377 = true := by decide +kernel

theorem c0378 : checkCell pa19 (cellAt 378) b0378 = true := by decide +kernel

theorem c0379 : checkCell pa19 (cellAt 379) b0379 = true := by decide +kernel

theorem c0380 : checkCell pa19 (cellAt 380) b0380 = true := by decide +kernel

theorem c0381 : checkCell pa19 (cellAt 381) b0381 = true := by decide +kernel

theorem c0382 : checkCell pa19 (cellAt 382) b0382 = true := by decide +kernel

theorem c0383 : checkCell pa19 (cellAt 383) b0383 = true := by decide +kernel

theorem c0384 : checkCell pa19 (cellAt 384) b0384 = true := by decide +kernel

theorem slice0375 : slice 375 10 = [cellAt 375, cellAt 376, cellAt 377, cellAt 378, cellAt 379, cellAt 380, cellAt 381, cellAt 382, cellAt 383, cellAt 384] := by decide +kernel

theorem batch0375_ok : checkAll pa19 (slice 375 10) breaks0375 = true := by
  rw [slice0375]
  simp only [breaks0375, checkAll, c0375, c0376, c0377, c0378, c0379, c0380, c0381, c0382, c0383, c0384, Bool.and_self]

theorem batch0375 : ∀ c ∈ slice 375 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0375_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0375
