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

/-! Serialized cells 975 to 984: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0975 : List ℚ := [2625/256]
def b0976 : List ℚ := [21075/2048]
def b0977 : List ℚ := [10575/1024]
def b0978 : List ℚ := [21225/2048]
def b0979 : List ℚ := [5325/512]
def b0980 : List ℚ := [21375/2048]
def b0981 : List ℚ := [10725/1024]
def b0982 : List ℚ := [21525/2048]
def b0983 : List ℚ := [675/64]
def b0984 : List ℚ := [21675/2048]

def breaks0975 : List (List ℚ) := [b0975, b0976, b0977, b0978, b0979, b0980, b0981, b0982, b0983, b0984]

theorem c0975 : checkCell pa19 (cellAt 975) b0975 = true := by decide +kernel

theorem c0976 : checkCell pa19 (cellAt 976) b0976 = true := by decide +kernel

theorem c0977 : checkCell pa19 (cellAt 977) b0977 = true := by decide +kernel

theorem c0978 : checkCell pa19 (cellAt 978) b0978 = true := by decide +kernel

theorem c0979 : checkCell pa19 (cellAt 979) b0979 = true := by decide +kernel

theorem c0980 : checkCell pa19 (cellAt 980) b0980 = true := by decide +kernel

theorem c0981 : checkCell pa19 (cellAt 981) b0981 = true := by decide +kernel

theorem c0982 : checkCell pa19 (cellAt 982) b0982 = true := by decide +kernel

theorem c0983 : checkCell pa19 (cellAt 983) b0983 = true := by decide +kernel

theorem c0984 : checkCell pa19 (cellAt 984) b0984 = true := by decide +kernel

theorem slice0975 : slice 975 10 = [cellAt 975, cellAt 976, cellAt 977, cellAt 978, cellAt 979, cellAt 980, cellAt 981, cellAt 982, cellAt 983, cellAt 984] := by decide +kernel

theorem batch0975_ok : checkAll pa19 (slice 975 10) breaks0975 = true := by
  rw [slice0975]
  simp only [breaks0975, checkAll, c0975, c0976, c0977, c0978, c0979, c0980, c0981, c0982, c0983, c0984, Bool.and_self]

theorem batch0975 : ∀ c ∈ slice 975 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0975_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0975
