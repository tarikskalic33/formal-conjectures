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

/-! Serialized cells 885 to 894: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0885 : List ℚ := [6975/1024]
def b0886 : List ℚ := [14025/2048]
def b0887 : List ℚ := [3525/512]
def b0888 : List ℚ := [14175/2048]
def b0889 : List ℚ := [7125/1024]
def b0890 : List ℚ := [14325/2048]
def b0891 : List ℚ := [225/32]
def b0892 : List ℚ := [14475/2048]
def b0893 : List ℚ := [7275/1024]
def b0894 : List ℚ := [14625/2048]

def breaks0885 : List (List ℚ) := [b0885, b0886, b0887, b0888, b0889, b0890, b0891, b0892, b0893, b0894]

theorem c0885 : checkCell pa19 (cellAt 885) b0885 = true := by decide +kernel

theorem c0886 : checkCell pa19 (cellAt 886) b0886 = true := by decide +kernel

theorem c0887 : checkCell pa19 (cellAt 887) b0887 = true := by decide +kernel

theorem c0888 : checkCell pa19 (cellAt 888) b0888 = true := by decide +kernel

theorem c0889 : checkCell pa19 (cellAt 889) b0889 = true := by decide +kernel

theorem c0890 : checkCell pa19 (cellAt 890) b0890 = true := by decide +kernel

theorem c0891 : checkCell pa19 (cellAt 891) b0891 = true := by decide +kernel

theorem c0892 : checkCell pa19 (cellAt 892) b0892 = true := by decide +kernel

theorem c0893 : checkCell pa19 (cellAt 893) b0893 = true := by decide +kernel

theorem c0894 : checkCell pa19 (cellAt 894) b0894 = true := by decide +kernel

theorem slice0885 : slice 885 10 = [cellAt 885, cellAt 886, cellAt 887, cellAt 888, cellAt 889, cellAt 890, cellAt 891, cellAt 892, cellAt 893, cellAt 894] := by decide +kernel

theorem batch0885_ok : checkAll pa19 (slice 885 10) breaks0885 = true := by
  rw [slice0885]
  simp only [breaks0885, checkAll, c0885, c0886, c0887, c0888, c0889, c0890, c0891, c0892, c0893, c0894, Bool.and_self]

theorem batch0885 : ∀ c ∈ slice 885 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0885_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0885
