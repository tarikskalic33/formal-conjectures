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

/-! Serialized cells 505 to 514: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0505 : List ℚ := [39375/32768]
def b0506 : List ℚ := [19725/16384]
def b0507 : List ℚ := [39525/32768]
def b0508 : List ℚ := [2475/2048]
def b0509 : List ℚ := [39675/32768]
def b0510 : List ℚ := [19875/16384]
def b0511 : List ℚ := [39825/32768]
def b0512 : List ℚ := [9975/8192]
def b0513 : List ℚ := [39975/32768]
def b0514 : List ℚ := [20025/16384]

def breaks0505 : List (List ℚ) := [b0505, b0506, b0507, b0508, b0509, b0510, b0511, b0512, b0513, b0514]

theorem c0505 : checkCell pa19 (cellAt 505) b0505 = true := by decide +kernel

theorem c0506 : checkCell pa19 (cellAt 506) b0506 = true := by decide +kernel

theorem c0507 : checkCell pa19 (cellAt 507) b0507 = true := by decide +kernel

theorem c0508 : checkCell pa19 (cellAt 508) b0508 = true := by decide +kernel

theorem c0509 : checkCell pa19 (cellAt 509) b0509 = true := by decide +kernel

theorem c0510 : checkCell pa19 (cellAt 510) b0510 = true := by decide +kernel

theorem c0511 : checkCell pa19 (cellAt 511) b0511 = true := by decide +kernel

theorem c0512 : checkCell pa19 (cellAt 512) b0512 = true := by decide +kernel

theorem c0513 : checkCell pa19 (cellAt 513) b0513 = true := by decide +kernel

theorem c0514 : checkCell pa19 (cellAt 514) b0514 = true := by decide +kernel

theorem slice0505 : slice 505 10 = [cellAt 505, cellAt 506, cellAt 507, cellAt 508, cellAt 509, cellAt 510, cellAt 511, cellAt 512, cellAt 513, cellAt 514] := by decide +kernel

theorem batch0505_ok : checkAll pa19 (slice 505 10) breaks0505 = true := by
  rw [slice0505]
  simp only [breaks0505, checkAll, c0505, c0506, c0507, c0508, c0509, c0510, c0511, c0512, c0513, c0514, Bool.and_self]

theorem batch0505 : ∀ c ∈ slice 505 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0505_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0505
