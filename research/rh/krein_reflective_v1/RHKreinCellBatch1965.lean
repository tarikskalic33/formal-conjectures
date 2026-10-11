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

/-! Serialized cells 1965 to 1974: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1965 : List ℚ := [59325/256]
def b1966 : List ℚ := [7425/32]
def b1967 : List ℚ := [59475/256]
def b1968 : List ℚ := [29775/128]
def b1969 : List ℚ := [59625/256]
def b1970 : List ℚ := [14925/64]
def b1971 : List ℚ := [59775/256]
def b1972 : List ℚ := [29925/128]
def b1973 : List ℚ := [59925/256]
def b1974 : List ℚ := [1875/8]

def breaks1965 : List (List ℚ) := [b1965, b1966, b1967, b1968, b1969, b1970, b1971, b1972, b1973, b1974]

theorem c1965 : checkCell pa19 (cellAt 1965) b1965 = true := by decide +kernel

theorem c1966 : checkCell pa19 (cellAt 1966) b1966 = true := by decide +kernel

theorem c1967 : checkCell pa19 (cellAt 1967) b1967 = true := by decide +kernel

theorem c1968 : checkCell pa19 (cellAt 1968) b1968 = true := by decide +kernel

theorem c1969 : checkCell pa19 (cellAt 1969) b1969 = true := by decide +kernel

theorem c1970 : checkCell pa19 (cellAt 1970) b1970 = true := by decide +kernel

theorem c1971 : checkCell pa19 (cellAt 1971) b1971 = true := by decide +kernel

theorem c1972 : checkCell pa19 (cellAt 1972) b1972 = true := by decide +kernel

theorem c1973 : checkCell pa19 (cellAt 1973) b1973 = true := by decide +kernel

theorem c1974 : checkCell pa19 (cellAt 1974) b1974 = true := by decide +kernel

theorem slice1965 : slice 1965 10 = [cellAt 1965, cellAt 1966, cellAt 1967, cellAt 1968, cellAt 1969, cellAt 1970, cellAt 1971, cellAt 1972, cellAt 1973, cellAt 1974] := by decide +kernel

theorem batch1965_ok : checkAll pa19 (slice 1965 10) breaks1965 = true := by
  rw [slice1965]
  simp only [breaks1965, checkAll, c1965, c1966, c1967, c1968, c1969, c1970, c1971, c1972, c1973, c1974, Bool.and_self]

theorem batch1965 : ∀ c ∈ slice 1965 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1965_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1965
