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

/-! Serialized cells 405 to 414: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0405 : List ℚ := [31875/32768]
def b0406 : List ℚ := [15975/16384]
def b0407 : List ℚ := [32025/32768]
def b0408 : List ℚ := [8025/8192]
def b0409 : List ℚ := [32175/32768]
def b0410 : List ℚ := [16125/16384]
def b0411 : List ℚ := [32325/32768]
def b0412 : List ℚ := [2025/2048]
def b0413 : List ℚ := [32475/32768]
def b0414 : List ℚ := [16275/16384]

def breaks0405 : List (List ℚ) := [b0405, b0406, b0407, b0408, b0409, b0410, b0411, b0412, b0413, b0414]

theorem c0405 : checkCell pa19 (cellAt 405) b0405 = true := by decide +kernel

theorem c0406 : checkCell pa19 (cellAt 406) b0406 = true := by decide +kernel

theorem c0407 : checkCell pa19 (cellAt 407) b0407 = true := by decide +kernel

theorem c0408 : checkCell pa19 (cellAt 408) b0408 = true := by decide +kernel

theorem c0409 : checkCell pa19 (cellAt 409) b0409 = true := by decide +kernel

theorem c0410 : checkCell pa19 (cellAt 410) b0410 = true := by decide +kernel

theorem c0411 : checkCell pa19 (cellAt 411) b0411 = true := by decide +kernel

theorem c0412 : checkCell pa19 (cellAt 412) b0412 = true := by decide +kernel

theorem c0413 : checkCell pa19 (cellAt 413) b0413 = true := by decide +kernel

theorem c0414 : checkCell pa19 (cellAt 414) b0414 = true := by decide +kernel

theorem slice0405 : slice 405 10 = [cellAt 405, cellAt 406, cellAt 407, cellAt 408, cellAt 409, cellAt 410, cellAt 411, cellAt 412, cellAt 413, cellAt 414] := by decide +kernel

theorem batch0405_ok : checkAll pa19 (slice 405 10) breaks0405 = true := by
  rw [slice0405]
  simp only [breaks0405, checkAll, c0405, c0406, c0407, c0408, c0409, c0410, c0411, c0412, c0413, c0414, Bool.and_self]

theorem batch0405 : ∀ c ∈ slice 405 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0405_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0405
