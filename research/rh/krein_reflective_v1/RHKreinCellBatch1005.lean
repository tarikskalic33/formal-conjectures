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

/-! Serialized cells 1005 to 1014: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1005 : List ℚ := [22725/2048]
def b1006 : List ℚ := [45525/4096]
def b1007 : List ℚ := [1425/128]
def b1008 : List ℚ := [45675/4096]
def b1009 : List ℚ := [22875/2048]
def b1010 : List ℚ := [45825/4096]
def b1011 : List ℚ := [11475/1024]
def b1012 : List ℚ := [45975/4096]
def b1013 : List ℚ := [23025/2048]
def b1014 : List ℚ := [46125/4096]

def breaks1005 : List (List ℚ) := [b1005, b1006, b1007, b1008, b1009, b1010, b1011, b1012, b1013, b1014]

theorem c1005 : checkCell pa19 (cellAt 1005) b1005 = true := by decide +kernel

theorem c1006 : checkCell pa19 (cellAt 1006) b1006 = true := by decide +kernel

theorem c1007 : checkCell pa19 (cellAt 1007) b1007 = true := by decide +kernel

theorem c1008 : checkCell pa19 (cellAt 1008) b1008 = true := by decide +kernel

theorem c1009 : checkCell pa19 (cellAt 1009) b1009 = true := by decide +kernel

theorem c1010 : checkCell pa19 (cellAt 1010) b1010 = true := by decide +kernel

theorem c1011 : checkCell pa19 (cellAt 1011) b1011 = true := by decide +kernel

theorem c1012 : checkCell pa19 (cellAt 1012) b1012 = true := by decide +kernel

theorem c1013 : checkCell pa19 (cellAt 1013) b1013 = true := by decide +kernel

theorem c1014 : checkCell pa19 (cellAt 1014) b1014 = true := by decide +kernel

theorem slice1005 : slice 1005 10 = [cellAt 1005, cellAt 1006, cellAt 1007, cellAt 1008, cellAt 1009, cellAt 1010, cellAt 1011, cellAt 1012, cellAt 1013, cellAt 1014] := by decide +kernel

theorem batch1005_ok : checkAll pa19 (slice 1005 10) breaks1005 = true := by
  rw [slice1005]
  simp only [breaks1005, checkAll, c1005, c1006, c1007, c1008, c1009, c1010, c1011, c1012, c1013, c1014, Bool.and_self]

theorem batch1005 : ∀ c ∈ slice 1005 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1005_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1005
