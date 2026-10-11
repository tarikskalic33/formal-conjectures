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

/-! Serialized cells 555 to 564: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0555 : List ℚ := [22575/16384]
def b0556 : List ℚ := [11325/8192]
def b0557 : List ℚ := [22725/16384]
def b0558 : List ℚ := [1425/1024]
def b0559 : List ℚ := [22875/16384]
def b0560 : List ℚ := [11475/8192]
def b0561 : List ℚ := [23025/16384]
def b0562 : List ℚ := [5775/4096]
def b0563 : List ℚ := [23175/16384]
def b0564 : List ℚ := [11625/8192]

def breaks0555 : List (List ℚ) := [b0555, b0556, b0557, b0558, b0559, b0560, b0561, b0562, b0563, b0564]

theorem c0555 : checkCell pa19 (cellAt 555) b0555 = true := by decide +kernel

theorem c0556 : checkCell pa19 (cellAt 556) b0556 = true := by decide +kernel

theorem c0557 : checkCell pa19 (cellAt 557) b0557 = true := by decide +kernel

theorem c0558 : checkCell pa19 (cellAt 558) b0558 = true := by decide +kernel

theorem c0559 : checkCell pa19 (cellAt 559) b0559 = true := by decide +kernel

theorem c0560 : checkCell pa19 (cellAt 560) b0560 = true := by decide +kernel

theorem c0561 : checkCell pa19 (cellAt 561) b0561 = true := by decide +kernel

theorem c0562 : checkCell pa19 (cellAt 562) b0562 = true := by decide +kernel

theorem c0563 : checkCell pa19 (cellAt 563) b0563 = true := by decide +kernel

theorem c0564 : checkCell pa19 (cellAt 564) b0564 = true := by decide +kernel

theorem slice0555 : slice 555 10 = [cellAt 555, cellAt 556, cellAt 557, cellAt 558, cellAt 559, cellAt 560, cellAt 561, cellAt 562, cellAt 563, cellAt 564] := by decide +kernel

theorem batch0555_ok : checkAll pa19 (slice 555 10) breaks0555 = true := by
  rw [slice0555]
  simp only [breaks0555, checkAll, c0555, c0556, c0557, c0558, c0559, c0560, c0561, c0562, c0563, c0564, Bool.and_self]

theorem batch0555 : ∀ c ∈ slice 555 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0555_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0555
