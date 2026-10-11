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

/-! Serialized cells 895 to 904: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0895 : List ℚ := [3675/512]
def b0896 : List ℚ := [14775/2048]
def b0897 : List ℚ := [7425/1024]
def b0898 : List ℚ := [14925/2048]
def b0899 : List ℚ := [1875/256]
def b0900 : List ℚ := [15075/2048]
def b0901 : List ℚ := [30225/4096]
def b0902 : List ℚ := [7575/1024]
def b0903 : List ℚ := [30375/4096]
def b0904 : List ℚ := [15225/2048]

def breaks0895 : List (List ℚ) := [b0895, b0896, b0897, b0898, b0899, b0900, b0901, b0902, b0903, b0904]

theorem c0895 : checkCell pa19 (cellAt 895) b0895 = true := by decide +kernel

theorem c0896 : checkCell pa19 (cellAt 896) b0896 = true := by decide +kernel

theorem c0897 : checkCell pa19 (cellAt 897) b0897 = true := by decide +kernel

theorem c0898 : checkCell pa19 (cellAt 898) b0898 = true := by decide +kernel

theorem c0899 : checkCell pa19 (cellAt 899) b0899 = true := by decide +kernel

theorem c0900 : checkCell pa19 (cellAt 900) b0900 = true := by decide +kernel

theorem c0901 : checkCell pa19 (cellAt 901) b0901 = true := by decide +kernel

theorem c0902 : checkCell pa19 (cellAt 902) b0902 = true := by decide +kernel

theorem c0903 : checkCell pa19 (cellAt 903) b0903 = true := by decide +kernel

theorem c0904 : checkCell pa19 (cellAt 904) b0904 = true := by decide +kernel

theorem slice0895 : slice 895 10 = [cellAt 895, cellAt 896, cellAt 897, cellAt 898, cellAt 899, cellAt 900, cellAt 901, cellAt 902, cellAt 903, cellAt 904] := by decide +kernel

theorem batch0895_ok : checkAll pa19 (slice 895 10) breaks0895 = true := by
  rw [slice0895]
  simp only [breaks0895, checkAll, c0895, c0896, c0897, c0898, c0899, c0900, c0901, c0902, c0903, c0904, Bool.and_self]

theorem batch0895 : ∀ c ∈ slice 895 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0895_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0895
