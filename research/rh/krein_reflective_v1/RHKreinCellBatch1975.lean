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

/-! Serialized cells 1975 to 1984: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1975 : List ℚ := [120075/512, 60075/256]
def b1976 : List ℚ := [120225/512, 30075/128]
def b1977 : List ℚ := [120375/512, 60225/256]
def b1978 : List ℚ := [120525/512, 15075/64]
def b1979 : List ℚ := [60375/256]
def b1980 : List ℚ := [30225/128]
def b1981 : List ℚ := [60525/256]
def b1982 : List ℚ := [7575/32]
def b1983 : List ℚ := [121275/512, 60675/256]
def b1984 : List ℚ := [121425/512, 30375/128]

def breaks1975 : List (List ℚ) := [b1975, b1976, b1977, b1978, b1979, b1980, b1981, b1982, b1983, b1984]

theorem c1975 : checkCell pa19 (cellAt 1975) b1975 = true := by decide +kernel

theorem c1976 : checkCell pa19 (cellAt 1976) b1976 = true := by decide +kernel

theorem c1977 : checkCell pa19 (cellAt 1977) b1977 = true := by decide +kernel

theorem c1978 : checkCell pa19 (cellAt 1978) b1978 = true := by decide +kernel

theorem c1979 : checkCell pa19 (cellAt 1979) b1979 = true := by decide +kernel

theorem c1980 : checkCell pa19 (cellAt 1980) b1980 = true := by decide +kernel

theorem c1981 : checkCell pa19 (cellAt 1981) b1981 = true := by decide +kernel

theorem c1982 : checkCell pa19 (cellAt 1982) b1982 = true := by decide +kernel

theorem c1983 : checkCell pa19 (cellAt 1983) b1983 = true := by decide +kernel

theorem c1984 : checkCell pa19 (cellAt 1984) b1984 = true := by decide +kernel

theorem slice1975 : slice 1975 10 = [cellAt 1975, cellAt 1976, cellAt 1977, cellAt 1978, cellAt 1979, cellAt 1980, cellAt 1981, cellAt 1982, cellAt 1983, cellAt 1984] := by decide +kernel

theorem batch1975_ok : checkAll pa19 (slice 1975 10) breaks1975 = true := by
  rw [slice1975]
  simp only [breaks1975, checkAll, c1975, c1976, c1977, c1978, c1979, c1980, c1981, c1982, c1983, c1984, Bool.and_self]

theorem batch1975 : ∀ c ∈ slice 1975 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1975_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1975
