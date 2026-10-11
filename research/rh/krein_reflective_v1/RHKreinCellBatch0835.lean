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

/-! Serialized cells 835 to 844: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0835 : List ℚ := [1275/256]
def b0836 : List ℚ := [10275/2048]
def b0837 : List ℚ := [5175/1024]
def b0838 : List ℚ := [10425/2048]
def b0839 : List ℚ := [2625/512]
def b0840 : List ℚ := [10575/2048]
def b0841 : List ℚ := [5325/1024]
def b0842 : List ℚ := [10725/2048]
def b0843 : List ℚ := [675/128]
def b0844 : List ℚ := [10875/2048]

def breaks0835 : List (List ℚ) := [b0835, b0836, b0837, b0838, b0839, b0840, b0841, b0842, b0843, b0844]

theorem c0835 : checkCell pa19 (cellAt 835) b0835 = true := by decide +kernel

theorem c0836 : checkCell pa19 (cellAt 836) b0836 = true := by decide +kernel

theorem c0837 : checkCell pa19 (cellAt 837) b0837 = true := by decide +kernel

theorem c0838 : checkCell pa19 (cellAt 838) b0838 = true := by decide +kernel

theorem c0839 : checkCell pa19 (cellAt 839) b0839 = true := by decide +kernel

theorem c0840 : checkCell pa19 (cellAt 840) b0840 = true := by decide +kernel

theorem c0841 : checkCell pa19 (cellAt 841) b0841 = true := by decide +kernel

theorem c0842 : checkCell pa19 (cellAt 842) b0842 = true := by decide +kernel

theorem c0843 : checkCell pa19 (cellAt 843) b0843 = true := by decide +kernel

theorem c0844 : checkCell pa19 (cellAt 844) b0844 = true := by decide +kernel

theorem slice0835 : slice 835 10 = [cellAt 835, cellAt 836, cellAt 837, cellAt 838, cellAt 839, cellAt 840, cellAt 841, cellAt 842, cellAt 843, cellAt 844] := by decide +kernel

theorem batch0835_ok : checkAll pa19 (slice 835 10) breaks0835 = true := by
  rw [slice0835]
  simp only [breaks0835, checkAll, c0835, c0836, c0837, c0838, c0839, c0840, c0841, c0842, c0843, c0844, Bool.and_self]

theorem batch0835 : ∀ c ∈ slice 835 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0835_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0835
