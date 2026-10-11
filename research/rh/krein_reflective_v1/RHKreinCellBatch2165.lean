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

/-! Serialized cells 2165 to 2174: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b2165 : List ℚ := [74325/256]
def b2166 : List ℚ := [2325/8]
def b2167 : List ℚ := [74475/256]
def b2168 : List ℚ := [37275/128]
def b2169 : List ℚ := [149175/512, 74625/256]
def b2170 : List ℚ := [149325/512, 18675/64]
def b2171 : List ℚ := [149475/512, 74775/256]
def b2172 : List ℚ := [37425/128]
def b2173 : List ℚ := [74925/256]
def b2174 : List ℚ := [9375/32]

def breaks2165 : List (List ℚ) := [b2165, b2166, b2167, b2168, b2169, b2170, b2171, b2172, b2173, b2174]

theorem c2165 : checkCell pa19 (cellAt 2165) b2165 = true := by decide +kernel

theorem c2166 : checkCell pa19 (cellAt 2166) b2166 = true := by decide +kernel

theorem c2167 : checkCell pa19 (cellAt 2167) b2167 = true := by decide +kernel

theorem c2168 : checkCell pa19 (cellAt 2168) b2168 = true := by decide +kernel

theorem c2169 : checkCell pa19 (cellAt 2169) b2169 = true := by decide +kernel

theorem c2170 : checkCell pa19 (cellAt 2170) b2170 = true := by decide +kernel

theorem c2171 : checkCell pa19 (cellAt 2171) b2171 = true := by decide +kernel

theorem c2172 : checkCell pa19 (cellAt 2172) b2172 = true := by decide +kernel

theorem c2173 : checkCell pa19 (cellAt 2173) b2173 = true := by decide +kernel

theorem c2174 : checkCell pa19 (cellAt 2174) b2174 = true := by decide +kernel

theorem slice2165 : slice 2165 10 = [cellAt 2165, cellAt 2166, cellAt 2167, cellAt 2168, cellAt 2169, cellAt 2170, cellAt 2171, cellAt 2172, cellAt 2173, cellAt 2174] := by decide +kernel

theorem batch2165_ok : checkAll pa19 (slice 2165 10) breaks2165 = true := by
  rw [slice2165]
  simp only [breaks2165, checkAll, c2165, c2166, c2167, c2168, c2169, c2170, c2171, c2172, c2173, c2174, Bool.and_self]

theorem batch2165 : ∀ c ∈ slice 2165 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch2165_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch2165
