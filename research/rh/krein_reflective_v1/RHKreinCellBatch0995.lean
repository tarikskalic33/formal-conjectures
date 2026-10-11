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

/-! Serialized cells 995 to 1004: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0995 : List ℚ := [11175/1024]
def b0996 : List ℚ := [44775/4096]
def b0997 : List ℚ := [22425/2048]
def b0998 : List ℚ := [44925/4096]
def b0999 : List ℚ := [5625/512]
def b1000 : List ℚ := [45075/4096]
def b1001 : List ℚ := [22575/2048]
def b1002 : List ℚ := [45225/4096]
def b1003 : List ℚ := [11325/1024]
def b1004 : List ℚ := [45375/4096]

def breaks0995 : List (List ℚ) := [b0995, b0996, b0997, b0998, b0999, b1000, b1001, b1002, b1003, b1004]

theorem c0995 : checkCell pa19 (cellAt 995) b0995 = true := by decide +kernel

theorem c0996 : checkCell pa19 (cellAt 996) b0996 = true := by decide +kernel

theorem c0997 : checkCell pa19 (cellAt 997) b0997 = true := by decide +kernel

theorem c0998 : checkCell pa19 (cellAt 998) b0998 = true := by decide +kernel

theorem c0999 : checkCell pa19 (cellAt 999) b0999 = true := by decide +kernel

theorem c1000 : checkCell pa19 (cellAt 1000) b1000 = true := by decide +kernel

theorem c1001 : checkCell pa19 (cellAt 1001) b1001 = true := by decide +kernel

theorem c1002 : checkCell pa19 (cellAt 1002) b1002 = true := by decide +kernel

theorem c1003 : checkCell pa19 (cellAt 1003) b1003 = true := by decide +kernel

theorem c1004 : checkCell pa19 (cellAt 1004) b1004 = true := by decide +kernel

theorem slice0995 : slice 995 10 = [cellAt 995, cellAt 996, cellAt 997, cellAt 998, cellAt 999, cellAt 1000, cellAt 1001, cellAt 1002, cellAt 1003, cellAt 1004] := by decide +kernel

theorem batch0995_ok : checkAll pa19 (slice 995 10) breaks0995 = true := by
  rw [slice0995]
  simp only [breaks0995, checkAll, c0995, c0996, c0997, c0998, c0999, c1000, c1001, c1002, c1003, c1004, Bool.and_self]

theorem batch0995 : ∀ c ∈ slice 995 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0995_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0995
