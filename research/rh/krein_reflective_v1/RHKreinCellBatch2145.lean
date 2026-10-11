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

/-! Serialized cells 2145 to 2154: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b2145 : List ℚ := [72825/256]
def b2146 : List ℚ := [18225/64]
def b2147 : List ℚ := [72975/256]
def b2148 : List ℚ := [36525/128]
def b2149 : List ℚ := [73125/256]
def b2150 : List ℚ := [4575/16]
def b2151 : List ℚ := [73275/256]
def b2152 : List ℚ := [36675/128]
def b2153 : List ℚ := [73425/256]
def b2154 : List ℚ := [18375/64]

def breaks2145 : List (List ℚ) := [b2145, b2146, b2147, b2148, b2149, b2150, b2151, b2152, b2153, b2154]

theorem c2145 : checkCell pa19 (cellAt 2145) b2145 = true := by decide +kernel

theorem c2146 : checkCell pa19 (cellAt 2146) b2146 = true := by decide +kernel

theorem c2147 : checkCell pa19 (cellAt 2147) b2147 = true := by decide +kernel

theorem c2148 : checkCell pa19 (cellAt 2148) b2148 = true := by decide +kernel

theorem c2149 : checkCell pa19 (cellAt 2149) b2149 = true := by decide +kernel

theorem c2150 : checkCell pa19 (cellAt 2150) b2150 = true := by decide +kernel

theorem c2151 : checkCell pa19 (cellAt 2151) b2151 = true := by decide +kernel

theorem c2152 : checkCell pa19 (cellAt 2152) b2152 = true := by decide +kernel

theorem c2153 : checkCell pa19 (cellAt 2153) b2153 = true := by decide +kernel

theorem c2154 : checkCell pa19 (cellAt 2154) b2154 = true := by decide +kernel

theorem slice2145 : slice 2145 10 = [cellAt 2145, cellAt 2146, cellAt 2147, cellAt 2148, cellAt 2149, cellAt 2150, cellAt 2151, cellAt 2152, cellAt 2153, cellAt 2154] := by decide +kernel

theorem batch2145_ok : checkAll pa19 (slice 2145 10) breaks2145 = true := by
  rw [slice2145]
  simp only [breaks2145, checkAll, c2145, c2146, c2147, c2148, c2149, c2150, c2151, c2152, c2153, c2154, Bool.and_self]

theorem batch2145 : ∀ c ∈ slice 2145 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch2145_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch2145
