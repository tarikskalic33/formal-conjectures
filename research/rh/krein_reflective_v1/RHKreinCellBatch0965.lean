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

/-! Serialized cells 965 to 974: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0965 : List ℚ := [10125/1024]
def b0966 : List ℚ := [20325/2048]
def b0967 : List ℚ := [1275/128]
def b0968 : List ℚ := [20475/2048]
def b0969 : List ℚ := [10275/1024]
def b0970 : List ℚ := [20625/2048]
def b0971 : List ℚ := [5175/512]
def b0972 : List ℚ := [20775/2048]
def b0973 : List ℚ := [10425/1024]
def b0974 : List ℚ := [20925/2048]

def breaks0965 : List (List ℚ) := [b0965, b0966, b0967, b0968, b0969, b0970, b0971, b0972, b0973, b0974]

theorem c0965 : checkCell pa19 (cellAt 965) b0965 = true := by decide +kernel

theorem c0966 : checkCell pa19 (cellAt 966) b0966 = true := by decide +kernel

theorem c0967 : checkCell pa19 (cellAt 967) b0967 = true := by decide +kernel

theorem c0968 : checkCell pa19 (cellAt 968) b0968 = true := by decide +kernel

theorem c0969 : checkCell pa19 (cellAt 969) b0969 = true := by decide +kernel

theorem c0970 : checkCell pa19 (cellAt 970) b0970 = true := by decide +kernel

theorem c0971 : checkCell pa19 (cellAt 971) b0971 = true := by decide +kernel

theorem c0972 : checkCell pa19 (cellAt 972) b0972 = true := by decide +kernel

theorem c0973 : checkCell pa19 (cellAt 973) b0973 = true := by decide +kernel

theorem c0974 : checkCell pa19 (cellAt 974) b0974 = true := by decide +kernel

theorem slice0965 : slice 965 10 = [cellAt 965, cellAt 966, cellAt 967, cellAt 968, cellAt 969, cellAt 970, cellAt 971, cellAt 972, cellAt 973, cellAt 974] := by decide +kernel

theorem batch0965_ok : checkAll pa19 (slice 965 10) breaks0965 = true := by
  rw [slice0965]
  simp only [breaks0965, checkAll, c0965, c0966, c0967, c0968, c0969, c0970, c0971, c0972, c0973, c0974, Bool.and_self]

theorem batch0965 : ∀ c ∈ slice 965 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0965_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0965
