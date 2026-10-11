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

/-! Serialized cells 615 to 624: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0615 : List ℚ := [27075/16384]
def b0616 : List ℚ := [13575/8192]
def b0617 : List ℚ := [27225/16384]
def b0618 : List ℚ := [6825/4096]
def b0619 : List ℚ := [27375/16384]
def b0620 : List ℚ := [13725/8192]
def b0621 : List ℚ := [27525/16384]
def b0622 : List ℚ := [1725/1024]
def b0623 : List ℚ := [27675/16384]
def b0624 : List ℚ := [13875/8192]

def breaks0615 : List (List ℚ) := [b0615, b0616, b0617, b0618, b0619, b0620, b0621, b0622, b0623, b0624]

theorem c0615 : checkCell pa19 (cellAt 615) b0615 = true := by decide +kernel

theorem c0616 : checkCell pa19 (cellAt 616) b0616 = true := by decide +kernel

theorem c0617 : checkCell pa19 (cellAt 617) b0617 = true := by decide +kernel

theorem c0618 : checkCell pa19 (cellAt 618) b0618 = true := by decide +kernel

theorem c0619 : checkCell pa19 (cellAt 619) b0619 = true := by decide +kernel

theorem c0620 : checkCell pa19 (cellAt 620) b0620 = true := by decide +kernel

theorem c0621 : checkCell pa19 (cellAt 621) b0621 = true := by decide +kernel

theorem c0622 : checkCell pa19 (cellAt 622) b0622 = true := by decide +kernel

theorem c0623 : checkCell pa19 (cellAt 623) b0623 = true := by decide +kernel

theorem c0624 : checkCell pa19 (cellAt 624) b0624 = true := by decide +kernel

theorem slice0615 : slice 615 10 = [cellAt 615, cellAt 616, cellAt 617, cellAt 618, cellAt 619, cellAt 620, cellAt 621, cellAt 622, cellAt 623, cellAt 624] := by decide +kernel

theorem batch0615_ok : checkAll pa19 (slice 615 10) breaks0615 = true := by
  rw [slice0615]
  simp only [breaks0615, checkAll, c0615, c0616, c0617, c0618, c0619, c0620, c0621, c0622, c0623, c0624, Bool.and_self]

theorem batch0615 : ∀ c ∈ slice 615 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0615_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0615
