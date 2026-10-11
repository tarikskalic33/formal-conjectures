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

/-! Serialized cells 2155 to 2164: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b2155 : List ℚ := [73575/256]
def b2156 : List ℚ := [36825/128]
def b2157 : List ℚ := [73725/256]
def b2158 : List ℚ := [9225/32]
def b2159 : List ℚ := [73875/256]
def b2160 : List ℚ := [36975/128]
def b2161 : List ℚ := [147975/512, 74025/256]
def b2162 : List ℚ := [148125/512, 18525/64]
def b2163 : List ℚ := [148275/512, 74175/256]
def b2164 : List ℚ := [148425/512, 37125/128]

def breaks2155 : List (List ℚ) := [b2155, b2156, b2157, b2158, b2159, b2160, b2161, b2162, b2163, b2164]

theorem c2155 : checkCell pa19 (cellAt 2155) b2155 = true := by decide +kernel

theorem c2156 : checkCell pa19 (cellAt 2156) b2156 = true := by decide +kernel

theorem c2157 : checkCell pa19 (cellAt 2157) b2157 = true := by decide +kernel

theorem c2158 : checkCell pa19 (cellAt 2158) b2158 = true := by decide +kernel

theorem c2159 : checkCell pa19 (cellAt 2159) b2159 = true := by decide +kernel

theorem c2160 : checkCell pa19 (cellAt 2160) b2160 = true := by decide +kernel

theorem c2161 : checkCell pa19 (cellAt 2161) b2161 = true := by decide +kernel

theorem c2162 : checkCell pa19 (cellAt 2162) b2162 = true := by decide +kernel

theorem c2163 : checkCell pa19 (cellAt 2163) b2163 = true := by decide +kernel

theorem c2164 : checkCell pa19 (cellAt 2164) b2164 = true := by decide +kernel

theorem slice2155 : slice 2155 10 = [cellAt 2155, cellAt 2156, cellAt 2157, cellAt 2158, cellAt 2159, cellAt 2160, cellAt 2161, cellAt 2162, cellAt 2163, cellAt 2164] := by decide +kernel

theorem batch2155_ok : checkAll pa19 (slice 2155 10) breaks2155 = true := by
  rw [slice2155]
  simp only [breaks2155, checkAll, c2155, c2156, c2157, c2158, c2159, c2160, c2161, c2162, c2163, c2164, Bool.and_self]

theorem batch2155 : ∀ c ∈ slice 2155 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch2155_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch2155
