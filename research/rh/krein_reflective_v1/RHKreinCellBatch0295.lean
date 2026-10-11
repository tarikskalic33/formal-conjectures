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

/-! Serialized cells 295 to 304: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0295 : List ℚ := [23625/32768]
def b0296 : List ℚ := [5925/8192]
def b0297 : List ℚ := [23775/32768]
def b0298 : List ℚ := [11925/16384]
def b0299 : List ℚ := [23925/32768]
def b0300 : List ℚ := [375/512]
def b0301 : List ℚ := [24075/32768]
def b0302 : List ℚ := [12075/16384]
def b0303 : List ℚ := [24225/32768]
def b0304 : List ℚ := [6075/8192]

def breaks0295 : List (List ℚ) := [b0295, b0296, b0297, b0298, b0299, b0300, b0301, b0302, b0303, b0304]

theorem c0295 : checkCell pa19 (cellAt 295) b0295 = true := by decide +kernel

theorem c0296 : checkCell pa19 (cellAt 296) b0296 = true := by decide +kernel

theorem c0297 : checkCell pa19 (cellAt 297) b0297 = true := by decide +kernel

theorem c0298 : checkCell pa19 (cellAt 298) b0298 = true := by decide +kernel

theorem c0299 : checkCell pa19 (cellAt 299) b0299 = true := by decide +kernel

theorem c0300 : checkCell pa19 (cellAt 300) b0300 = true := by decide +kernel

theorem c0301 : checkCell pa19 (cellAt 301) b0301 = true := by decide +kernel

theorem c0302 : checkCell pa19 (cellAt 302) b0302 = true := by decide +kernel

theorem c0303 : checkCell pa19 (cellAt 303) b0303 = true := by decide +kernel

theorem c0304 : checkCell pa19 (cellAt 304) b0304 = true := by decide +kernel

theorem slice0295 : slice 295 10 = [cellAt 295, cellAt 296, cellAt 297, cellAt 298, cellAt 299, cellAt 300, cellAt 301, cellAt 302, cellAt 303, cellAt 304] := by decide +kernel

theorem batch0295_ok : checkAll pa19 (slice 295 10) breaks0295 = true := by
  rw [slice0295]
  simp only [breaks0295, checkAll, c0295, c0296, c0297, c0298, c0299, c0300, c0301, c0302, c0303, c0304, Bool.and_self]

theorem batch0295 : ∀ c ∈ slice 295 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0295_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0295
