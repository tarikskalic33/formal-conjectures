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

/-! Serialized cells 875 to 884: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0875 : List ℚ := [825/128]
def b0876 : List ℚ := [13275/2048]
def b0877 : List ℚ := [6675/1024]
def b0878 : List ℚ := [13425/2048]
def b0879 : List ℚ := [3375/512]
def b0880 : List ℚ := [13575/2048]
def b0881 : List ℚ := [6825/1024]
def b0882 : List ℚ := [13725/2048]
def b0883 : List ℚ := [1725/256]
def b0884 : List ℚ := [13875/2048]

def breaks0875 : List (List ℚ) := [b0875, b0876, b0877, b0878, b0879, b0880, b0881, b0882, b0883, b0884]

theorem c0875 : checkCell pa19 (cellAt 875) b0875 = true := by decide +kernel

theorem c0876 : checkCell pa19 (cellAt 876) b0876 = true := by decide +kernel

theorem c0877 : checkCell pa19 (cellAt 877) b0877 = true := by decide +kernel

theorem c0878 : checkCell pa19 (cellAt 878) b0878 = true := by decide +kernel

theorem c0879 : checkCell pa19 (cellAt 879) b0879 = true := by decide +kernel

theorem c0880 : checkCell pa19 (cellAt 880) b0880 = true := by decide +kernel

theorem c0881 : checkCell pa19 (cellAt 881) b0881 = true := by decide +kernel

theorem c0882 : checkCell pa19 (cellAt 882) b0882 = true := by decide +kernel

theorem c0883 : checkCell pa19 (cellAt 883) b0883 = true := by decide +kernel

theorem c0884 : checkCell pa19 (cellAt 884) b0884 = true := by decide +kernel

theorem slice0875 : slice 875 10 = [cellAt 875, cellAt 876, cellAt 877, cellAt 878, cellAt 879, cellAt 880, cellAt 881, cellAt 882, cellAt 883, cellAt 884] := by decide +kernel

theorem batch0875_ok : checkAll pa19 (slice 875 10) breaks0875 = true := by
  rw [slice0875]
  simp only [breaks0875, checkAll, c0875, c0876, c0877, c0878, c0879, c0880, c0881, c0882, c0883, c0884, Bool.and_self]

theorem batch0875 : ∀ c ∈ slice 875 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0875_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0875
