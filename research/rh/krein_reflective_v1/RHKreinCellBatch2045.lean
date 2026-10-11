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

/-! Serialized cells 2045 to 2054: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b2045 : List ℚ := [65325/256]
def b2046 : List ℚ := [8175/32]
def b2047 : List ℚ := [65475/256]
def b2048 : List ℚ := [32775/128]
def b2049 : List ℚ := [65625/256]
def b2050 : List ℚ := [16425/64]
def b2051 : List ℚ := [65775/256]
def b2052 : List ℚ := [32925/128]
def b2053 : List ℚ := [65925/256]
def b2054 : List ℚ := [4125/16]

def breaks2045 : List (List ℚ) := [b2045, b2046, b2047, b2048, b2049, b2050, b2051, b2052, b2053, b2054]

theorem c2045 : checkCell pa19 (cellAt 2045) b2045 = true := by decide +kernel

theorem c2046 : checkCell pa19 (cellAt 2046) b2046 = true := by decide +kernel

theorem c2047 : checkCell pa19 (cellAt 2047) b2047 = true := by decide +kernel

theorem c2048 : checkCell pa19 (cellAt 2048) b2048 = true := by decide +kernel

theorem c2049 : checkCell pa19 (cellAt 2049) b2049 = true := by decide +kernel

theorem c2050 : checkCell pa19 (cellAt 2050) b2050 = true := by decide +kernel

theorem c2051 : checkCell pa19 (cellAt 2051) b2051 = true := by decide +kernel

theorem c2052 : checkCell pa19 (cellAt 2052) b2052 = true := by decide +kernel

theorem c2053 : checkCell pa19 (cellAt 2053) b2053 = true := by decide +kernel

theorem c2054 : checkCell pa19 (cellAt 2054) b2054 = true := by decide +kernel

theorem slice2045 : slice 2045 10 = [cellAt 2045, cellAt 2046, cellAt 2047, cellAt 2048, cellAt 2049, cellAt 2050, cellAt 2051, cellAt 2052, cellAt 2053, cellAt 2054] := by decide +kernel

theorem batch2045_ok : checkAll pa19 (slice 2045 10) breaks2045 = true := by
  rw [slice2045]
  simp only [breaks2045, checkAll, c2045, c2046, c2047, c2048, c2049, c2050, c2051, c2052, c2053, c2054, Bool.and_self]

theorem batch2045 : ∀ c ∈ slice 2045 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch2045_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch2045
