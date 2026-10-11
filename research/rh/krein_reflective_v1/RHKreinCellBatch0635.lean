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

/-! Serialized cells 635 to 644: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0635 : List ℚ := [28575/16384]
def b0636 : List ℚ := [14325/8192]
def b0637 : List ℚ := [28725/16384]
def b0638 : List ℚ := [225/128]
def b0639 : List ℚ := [28875/16384]
def b0640 : List ℚ := [14475/8192]
def b0641 : List ℚ := [29025/16384]
def b0642 : List ℚ := [7275/4096]
def b0643 : List ℚ := [29175/16384]
def b0644 : List ℚ := [14625/8192]

def breaks0635 : List (List ℚ) := [b0635, b0636, b0637, b0638, b0639, b0640, b0641, b0642, b0643, b0644]

theorem c0635 : checkCell pa19 (cellAt 635) b0635 = true := by decide +kernel

theorem c0636 : checkCell pa19 (cellAt 636) b0636 = true := by decide +kernel

theorem c0637 : checkCell pa19 (cellAt 637) b0637 = true := by decide +kernel

theorem c0638 : checkCell pa19 (cellAt 638) b0638 = true := by decide +kernel

theorem c0639 : checkCell pa19 (cellAt 639) b0639 = true := by decide +kernel

theorem c0640 : checkCell pa19 (cellAt 640) b0640 = true := by decide +kernel

theorem c0641 : checkCell pa19 (cellAt 641) b0641 = true := by decide +kernel

theorem c0642 : checkCell pa19 (cellAt 642) b0642 = true := by decide +kernel

theorem c0643 : checkCell pa19 (cellAt 643) b0643 = true := by decide +kernel

theorem c0644 : checkCell pa19 (cellAt 644) b0644 = true := by decide +kernel

theorem slice0635 : slice 635 10 = [cellAt 635, cellAt 636, cellAt 637, cellAt 638, cellAt 639, cellAt 640, cellAt 641, cellAt 642, cellAt 643, cellAt 644] := by decide +kernel

theorem batch0635_ok : checkAll pa19 (slice 635 10) breaks0635 = true := by
  rw [slice0635]
  simp only [breaks0635, checkAll, c0635, c0636, c0637, c0638, c0639, c0640, c0641, c0642, c0643, c0644, Bool.and_self]

theorem batch0635 : ∀ c ∈ slice 635 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0635_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0635
