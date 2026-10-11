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

/-! Serialized cells 2055 to 2064: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b2055 : List ℚ := [66075/256]
def b2056 : List ℚ := [33075/128]
def b2057 : List ℚ := [66225/256]
def b2058 : List ℚ := [16575/64]
def b2059 : List ℚ := [66375/256]
def b2060 : List ℚ := [33225/128]
def b2061 : List ℚ := [66525/256]
def b2062 : List ℚ := [8325/32]
def b2063 : List ℚ := [66675/256]
def b2064 : List ℚ := [33375/128]

def breaks2055 : List (List ℚ) := [b2055, b2056, b2057, b2058, b2059, b2060, b2061, b2062, b2063, b2064]

theorem c2055 : checkCell pa19 (cellAt 2055) b2055 = true := by decide +kernel

theorem c2056 : checkCell pa19 (cellAt 2056) b2056 = true := by decide +kernel

theorem c2057 : checkCell pa19 (cellAt 2057) b2057 = true := by decide +kernel

theorem c2058 : checkCell pa19 (cellAt 2058) b2058 = true := by decide +kernel

theorem c2059 : checkCell pa19 (cellAt 2059) b2059 = true := by decide +kernel

theorem c2060 : checkCell pa19 (cellAt 2060) b2060 = true := by decide +kernel

theorem c2061 : checkCell pa19 (cellAt 2061) b2061 = true := by decide +kernel

theorem c2062 : checkCell pa19 (cellAt 2062) b2062 = true := by decide +kernel

theorem c2063 : checkCell pa19 (cellAt 2063) b2063 = true := by decide +kernel

theorem c2064 : checkCell pa19 (cellAt 2064) b2064 = true := by decide +kernel

theorem slice2055 : slice 2055 10 = [cellAt 2055, cellAt 2056, cellAt 2057, cellAt 2058, cellAt 2059, cellAt 2060, cellAt 2061, cellAt 2062, cellAt 2063, cellAt 2064] := by decide +kernel

theorem batch2055_ok : checkAll pa19 (slice 2055 10) breaks2055 = true := by
  rw [slice2055]
  simp only [breaks2055, checkAll, c2055, c2056, c2057, c2058, c2059, c2060, c2061, c2062, c2063, c2064, Bool.and_self]

theorem batch2055 : ∀ c ∈ slice 2055 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch2055_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch2055
