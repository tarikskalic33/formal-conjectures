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

/-! Serialized cells 955 to 964: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0955 : List ℚ := [75/8]
def b0956 : List ℚ := [9675/1024]
def b0957 : List ℚ := [4875/512]
def b0958 : List ℚ := [9825/1024]
def b0959 : List ℚ := [2475/256]
def b0960 : List ℚ := [19875/2048]
def b0961 : List ℚ := [9975/1024]
def b0962 : List ℚ := [20025/2048]
def b0963 : List ℚ := [5025/512]
def b0964 : List ℚ := [20175/2048]

def breaks0955 : List (List ℚ) := [b0955, b0956, b0957, b0958, b0959, b0960, b0961, b0962, b0963, b0964]

theorem c0955 : checkCell pa19 (cellAt 955) b0955 = true := by decide +kernel

theorem c0956 : checkCell pa19 (cellAt 956) b0956 = true := by decide +kernel

theorem c0957 : checkCell pa19 (cellAt 957) b0957 = true := by decide +kernel

theorem c0958 : checkCell pa19 (cellAt 958) b0958 = true := by decide +kernel

theorem c0959 : checkCell pa19 (cellAt 959) b0959 = true := by decide +kernel

theorem c0960 : checkCell pa19 (cellAt 960) b0960 = true := by decide +kernel

theorem c0961 : checkCell pa19 (cellAt 961) b0961 = true := by decide +kernel

theorem c0962 : checkCell pa19 (cellAt 962) b0962 = true := by decide +kernel

theorem c0963 : checkCell pa19 (cellAt 963) b0963 = true := by decide +kernel

theorem c0964 : checkCell pa19 (cellAt 964) b0964 = true := by decide +kernel

theorem slice0955 : slice 955 10 = [cellAt 955, cellAt 956, cellAt 957, cellAt 958, cellAt 959, cellAt 960, cellAt 961, cellAt 962, cellAt 963, cellAt 964] := by decide +kernel

theorem batch0955_ok : checkAll pa19 (slice 955 10) breaks0955 = true := by
  rw [slice0955]
  simp only [breaks0955, checkAll, c0955, c0956, c0957, c0958, c0959, c0960, c0961, c0962, c0963, c0964, Bool.and_self]

theorem batch0955 : ∀ c ∈ slice 955 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0955_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0955
