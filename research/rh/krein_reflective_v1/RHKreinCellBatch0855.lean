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

/-! Serialized cells 855 to 864: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0855 : List ℚ := [2925/512]
def b0856 : List ℚ := [11775/2048]
def b0857 : List ℚ := [5925/1024]
def b0858 : List ℚ := [11925/2048]
def b0859 : List ℚ := [375/64]
def b0860 : List ℚ := [12075/2048]
def b0861 : List ℚ := [6075/1024]
def b0862 : List ℚ := [12225/2048]
def b0863 : List ℚ := [3075/512]
def b0864 : List ℚ := [12375/2048]

def breaks0855 : List (List ℚ) := [b0855, b0856, b0857, b0858, b0859, b0860, b0861, b0862, b0863, b0864]

theorem c0855 : checkCell pa19 (cellAt 855) b0855 = true := by decide +kernel

theorem c0856 : checkCell pa19 (cellAt 856) b0856 = true := by decide +kernel

theorem c0857 : checkCell pa19 (cellAt 857) b0857 = true := by decide +kernel

theorem c0858 : checkCell pa19 (cellAt 858) b0858 = true := by decide +kernel

theorem c0859 : checkCell pa19 (cellAt 859) b0859 = true := by decide +kernel

theorem c0860 : checkCell pa19 (cellAt 860) b0860 = true := by decide +kernel

theorem c0861 : checkCell pa19 (cellAt 861) b0861 = true := by decide +kernel

theorem c0862 : checkCell pa19 (cellAt 862) b0862 = true := by decide +kernel

theorem c0863 : checkCell pa19 (cellAt 863) b0863 = true := by decide +kernel

theorem c0864 : checkCell pa19 (cellAt 864) b0864 = true := by decide +kernel

theorem slice0855 : slice 855 10 = [cellAt 855, cellAt 856, cellAt 857, cellAt 858, cellAt 859, cellAt 860, cellAt 861, cellAt 862, cellAt 863, cellAt 864] := by decide +kernel

theorem batch0855_ok : checkAll pa19 (slice 855 10) breaks0855 = true := by
  rw [slice0855]
  simp only [breaks0855, checkAll, c0855, c0856, c0857, c0858, c0859, c0860, c0861, c0862, c0863, c0864, Bool.and_self]

theorem batch0855 : ∀ c ∈ slice 855 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0855_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0855
