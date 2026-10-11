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

/-! Serialized cells 1955 to 1964: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1955 : List ℚ := [58575/256]
def b1956 : List ℚ := [29325/128]
def b1957 : List ℚ := [58725/256]
def b1958 : List ℚ := [3675/16]
def b1959 : List ℚ := [58875/256]
def b1960 : List ℚ := [29475/128]
def b1961 : List ℚ := [59025/256]
def b1962 : List ℚ := [14775/64]
def b1963 : List ℚ := [59175/256]
def b1964 : List ℚ := [29625/128]

def breaks1955 : List (List ℚ) := [b1955, b1956, b1957, b1958, b1959, b1960, b1961, b1962, b1963, b1964]

theorem c1955 : checkCell pa19 (cellAt 1955) b1955 = true := by decide +kernel

theorem c1956 : checkCell pa19 (cellAt 1956) b1956 = true := by decide +kernel

theorem c1957 : checkCell pa19 (cellAt 1957) b1957 = true := by decide +kernel

theorem c1958 : checkCell pa19 (cellAt 1958) b1958 = true := by decide +kernel

theorem c1959 : checkCell pa19 (cellAt 1959) b1959 = true := by decide +kernel

theorem c1960 : checkCell pa19 (cellAt 1960) b1960 = true := by decide +kernel

theorem c1961 : checkCell pa19 (cellAt 1961) b1961 = true := by decide +kernel

theorem c1962 : checkCell pa19 (cellAt 1962) b1962 = true := by decide +kernel

theorem c1963 : checkCell pa19 (cellAt 1963) b1963 = true := by decide +kernel

theorem c1964 : checkCell pa19 (cellAt 1964) b1964 = true := by decide +kernel

theorem slice1955 : slice 1955 10 = [cellAt 1955, cellAt 1956, cellAt 1957, cellAt 1958, cellAt 1959, cellAt 1960, cellAt 1961, cellAt 1962, cellAt 1963, cellAt 1964] := by decide +kernel

theorem batch1955_ok : checkAll pa19 (slice 1955 10) breaks1955 = true := by
  rw [slice1955]
  simp only [breaks1955, checkAll, c1955, c1956, c1957, c1958, c1959, c1960, c1961, c1962, c1963, c1964, Bool.and_self]

theorem batch1955 : ∀ c ∈ slice 1955 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1955_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1955
