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

/-! Serialized cells 1015 to 1024: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1015 : List ℚ := [5775/512]
def b1016 : List ℚ := [46275/4096]
def b1017 : List ℚ := [23175/2048]
def b1018 : List ℚ := [46425/4096]
def b1019 : List ℚ := [11625/1024]
def b1020 : List ℚ := [46575/4096]
def b1021 : List ℚ := [23325/2048]
def b1022 : List ℚ := [46725/4096]
def b1023 : List ℚ := [2925/256]
def b1024 : List ℚ := [46875/4096]

def breaks1015 : List (List ℚ) := [b1015, b1016, b1017, b1018, b1019, b1020, b1021, b1022, b1023, b1024]

theorem c1015 : checkCell pa19 (cellAt 1015) b1015 = true := by decide +kernel

theorem c1016 : checkCell pa19 (cellAt 1016) b1016 = true := by decide +kernel

theorem c1017 : checkCell pa19 (cellAt 1017) b1017 = true := by decide +kernel

theorem c1018 : checkCell pa19 (cellAt 1018) b1018 = true := by decide +kernel

theorem c1019 : checkCell pa19 (cellAt 1019) b1019 = true := by decide +kernel

theorem c1020 : checkCell pa19 (cellAt 1020) b1020 = true := by decide +kernel

theorem c1021 : checkCell pa19 (cellAt 1021) b1021 = true := by decide +kernel

theorem c1022 : checkCell pa19 (cellAt 1022) b1022 = true := by decide +kernel

theorem c1023 : checkCell pa19 (cellAt 1023) b1023 = true := by decide +kernel

theorem c1024 : checkCell pa19 (cellAt 1024) b1024 = true := by decide +kernel

theorem slice1015 : slice 1015 10 = [cellAt 1015, cellAt 1016, cellAt 1017, cellAt 1018, cellAt 1019, cellAt 1020, cellAt 1021, cellAt 1022, cellAt 1023, cellAt 1024] := by decide +kernel

theorem batch1015_ok : checkAll pa19 (slice 1015 10) breaks1015 = true := by
  rw [slice1015]
  simp only [breaks1015, checkAll, c1015, c1016, c1017, c1018, c1019, c1020, c1021, c1022, c1023, c1024, Bool.and_self]

theorem batch1015 : ∀ c ∈ slice 1015 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1015_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1015
