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

/-! Serialized cells 905 to 914: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0905 : List ℚ := [30525/4096]
def b0906 : List ℚ := [3825/512]
def b0907 : List ℚ := [30675/4096]
def b0908 : List ℚ := [15375/2048]
def b0909 : List ℚ := [30825/4096]
def b0910 : List ℚ := [7725/1024]
def b0911 : List ℚ := [30975/4096]
def b0912 : List ℚ := [15525/2048]
def b0913 : List ℚ := [31125/4096]
def b0914 : List ℚ := [975/128]

def breaks0905 : List (List ℚ) := [b0905, b0906, b0907, b0908, b0909, b0910, b0911, b0912, b0913, b0914]

theorem c0905 : checkCell pa19 (cellAt 905) b0905 = true := by decide +kernel

theorem c0906 : checkCell pa19 (cellAt 906) b0906 = true := by decide +kernel

theorem c0907 : checkCell pa19 (cellAt 907) b0907 = true := by decide +kernel

theorem c0908 : checkCell pa19 (cellAt 908) b0908 = true := by decide +kernel

theorem c0909 : checkCell pa19 (cellAt 909) b0909 = true := by decide +kernel

theorem c0910 : checkCell pa19 (cellAt 910) b0910 = true := by decide +kernel

theorem c0911 : checkCell pa19 (cellAt 911) b0911 = true := by decide +kernel

theorem c0912 : checkCell pa19 (cellAt 912) b0912 = true := by decide +kernel

theorem c0913 : checkCell pa19 (cellAt 913) b0913 = true := by decide +kernel

theorem c0914 : checkCell pa19 (cellAt 914) b0914 = true := by decide +kernel

theorem slice0905 : slice 905 10 = [cellAt 905, cellAt 906, cellAt 907, cellAt 908, cellAt 909, cellAt 910, cellAt 911, cellAt 912, cellAt 913, cellAt 914] := by decide +kernel

theorem batch0905_ok : checkAll pa19 (slice 905 10) breaks0905 = true := by
  rw [slice0905]
  simp only [breaks0905, checkAll, c0905, c0906, c0907, c0908, c0909, c0910, c0911, c0912, c0913, c0914, Bool.and_self]

theorem batch0905 : ∀ c ∈ slice 905 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0905_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0905
