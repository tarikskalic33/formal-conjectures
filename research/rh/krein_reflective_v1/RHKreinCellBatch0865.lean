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

/-! Serialized cells 865 to 874: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0865 : List ℚ := [6225/1024]
def b0866 : List ℚ := [12525/2048]
def b0867 : List ℚ := [1575/256]
def b0868 : List ℚ := [12675/2048]
def b0869 : List ℚ := [6375/1024]
def b0870 : List ℚ := [12825/2048]
def b0871 : List ℚ := [3225/512]
def b0872 : List ℚ := [12975/2048]
def b0873 : List ℚ := [6525/1024]
def b0874 : List ℚ := [13125/2048]

def breaks0865 : List (List ℚ) := [b0865, b0866, b0867, b0868, b0869, b0870, b0871, b0872, b0873, b0874]

theorem c0865 : checkCell pa19 (cellAt 865) b0865 = true := by decide +kernel

theorem c0866 : checkCell pa19 (cellAt 866) b0866 = true := by decide +kernel

theorem c0867 : checkCell pa19 (cellAt 867) b0867 = true := by decide +kernel

theorem c0868 : checkCell pa19 (cellAt 868) b0868 = true := by decide +kernel

theorem c0869 : checkCell pa19 (cellAt 869) b0869 = true := by decide +kernel

theorem c0870 : checkCell pa19 (cellAt 870) b0870 = true := by decide +kernel

theorem c0871 : checkCell pa19 (cellAt 871) b0871 = true := by decide +kernel

theorem c0872 : checkCell pa19 (cellAt 872) b0872 = true := by decide +kernel

theorem c0873 : checkCell pa19 (cellAt 873) b0873 = true := by decide +kernel

theorem c0874 : checkCell pa19 (cellAt 874) b0874 = true := by decide +kernel

theorem slice0865 : slice 865 10 = [cellAt 865, cellAt 866, cellAt 867, cellAt 868, cellAt 869, cellAt 870, cellAt 871, cellAt 872, cellAt 873, cellAt 874] := by decide +kernel

theorem batch0865_ok : checkAll pa19 (slice 865 10) breaks0865 = true := by
  rw [slice0865]
  simp only [breaks0865, checkAll, c0865, c0866, c0867, c0868, c0869, c0870, c0871, c0872, c0873, c0874, Bool.and_self]

theorem batch0865 : ∀ c ∈ slice 865 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0865_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0865
