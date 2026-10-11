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

/-! Serialized cells 985 to 994: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0985 : List ℚ := [10875/1024]
def b0986 : List ℚ := [21825/2048]
def b0987 : List ℚ := [5475/512]
def b0988 : List ℚ := [21975/2048]
def b0989 : List ℚ := [11025/1024]
def b0990 : List ℚ := [22125/2048]
def b0991 : List ℚ := [2775/256]
def b0992 : List ℚ := [44475/4096]
def b0993 : List ℚ := [22275/2048]
def b0994 : List ℚ := [44625/4096]

def breaks0985 : List (List ℚ) := [b0985, b0986, b0987, b0988, b0989, b0990, b0991, b0992, b0993, b0994]

theorem c0985 : checkCell pa19 (cellAt 985) b0985 = true := by decide +kernel

theorem c0986 : checkCell pa19 (cellAt 986) b0986 = true := by decide +kernel

theorem c0987 : checkCell pa19 (cellAt 987) b0987 = true := by decide +kernel

theorem c0988 : checkCell pa19 (cellAt 988) b0988 = true := by decide +kernel

theorem c0989 : checkCell pa19 (cellAt 989) b0989 = true := by decide +kernel

theorem c0990 : checkCell pa19 (cellAt 990) b0990 = true := by decide +kernel

theorem c0991 : checkCell pa19 (cellAt 991) b0991 = true := by decide +kernel

theorem c0992 : checkCell pa19 (cellAt 992) b0992 = true := by decide +kernel

theorem c0993 : checkCell pa19 (cellAt 993) b0993 = true := by decide +kernel

theorem c0994 : checkCell pa19 (cellAt 994) b0994 = true := by decide +kernel

theorem slice0985 : slice 985 10 = [cellAt 985, cellAt 986, cellAt 987, cellAt 988, cellAt 989, cellAt 990, cellAt 991, cellAt 992, cellAt 993, cellAt 994] := by decide +kernel

theorem batch0985_ok : checkAll pa19 (slice 985 10) breaks0985 = true := by
  rw [slice0985]
  simp only [breaks0985, checkAll, c0985, c0986, c0987, c0988, c0989, c0990, c0991, c0992, c0993, c0994, Bool.and_self]

theorem batch0985 : ∀ c ∈ slice 985 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0985_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0985
