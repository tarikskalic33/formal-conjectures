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

/-! Serialized cells 715 to 724: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0715 : List ℚ := [4875/2048]
def b0716 : List ℚ := [9825/4096]
def b0717 : List ℚ := [2475/1024]
def b0718 : List ℚ := [9975/4096]
def b0719 : List ℚ := [5025/2048]
def b0720 : List ℚ := [10125/4096]
def b0721 : List ℚ := [1275/512]
def b0722 : List ℚ := [10275/4096]
def b0723 : List ℚ := [5175/2048]
def b0724 : List ℚ := [10425/4096]

def breaks0715 : List (List ℚ) := [b0715, b0716, b0717, b0718, b0719, b0720, b0721, b0722, b0723, b0724]

theorem c0715 : checkCell pa19 (cellAt 715) b0715 = true := by decide +kernel

theorem c0716 : checkCell pa19 (cellAt 716) b0716 = true := by decide +kernel

theorem c0717 : checkCell pa19 (cellAt 717) b0717 = true := by decide +kernel

theorem c0718 : checkCell pa19 (cellAt 718) b0718 = true := by decide +kernel

theorem c0719 : checkCell pa19 (cellAt 719) b0719 = true := by decide +kernel

theorem c0720 : checkCell pa19 (cellAt 720) b0720 = true := by decide +kernel

theorem c0721 : checkCell pa19 (cellAt 721) b0721 = true := by decide +kernel

theorem c0722 : checkCell pa19 (cellAt 722) b0722 = true := by decide +kernel

theorem c0723 : checkCell pa19 (cellAt 723) b0723 = true := by decide +kernel

theorem c0724 : checkCell pa19 (cellAt 724) b0724 = true := by decide +kernel

theorem slice0715 : slice 715 10 = [cellAt 715, cellAt 716, cellAt 717, cellAt 718, cellAt 719, cellAt 720, cellAt 721, cellAt 722, cellAt 723, cellAt 724] := by decide +kernel

theorem batch0715_ok : checkAll pa19 (slice 715 10) breaks0715 = true := by
  rw [slice0715]
  simp only [breaks0715, checkAll, c0715, c0716, c0717, c0718, c0719, c0720, c0721, c0722, c0723, c0724, Bool.and_self]

theorem batch0715 : ∀ c ∈ slice 715 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0715_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0715
