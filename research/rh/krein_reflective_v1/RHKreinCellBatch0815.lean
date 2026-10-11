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

/-! Serialized cells 815 to 824: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0815 : List ℚ := [8775/2048]
def b0816 : List ℚ := [17625/4096]
def b0817 : List ℚ := [4425/1024]
def b0818 : List ℚ := [8925/2048]
def b0819 : List ℚ := [1125/256]
def b0820 : List ℚ := [9075/2048]
def b0821 : List ℚ := [4575/1024]
def b0822 : List ℚ := [9225/2048]
def b0823 : List ℚ := [2325/512]
def b0824 : List ℚ := [9375/2048]

def breaks0815 : List (List ℚ) := [b0815, b0816, b0817, b0818, b0819, b0820, b0821, b0822, b0823, b0824]

theorem c0815 : checkCell pa19 (cellAt 815) b0815 = true := by decide +kernel

theorem c0816 : checkCell pa19 (cellAt 816) b0816 = true := by decide +kernel

theorem c0817 : checkCell pa19 (cellAt 817) b0817 = true := by decide +kernel

theorem c0818 : checkCell pa19 (cellAt 818) b0818 = true := by decide +kernel

theorem c0819 : checkCell pa19 (cellAt 819) b0819 = true := by decide +kernel

theorem c0820 : checkCell pa19 (cellAt 820) b0820 = true := by decide +kernel

theorem c0821 : checkCell pa19 (cellAt 821) b0821 = true := by decide +kernel

theorem c0822 : checkCell pa19 (cellAt 822) b0822 = true := by decide +kernel

theorem c0823 : checkCell pa19 (cellAt 823) b0823 = true := by decide +kernel

theorem c0824 : checkCell pa19 (cellAt 824) b0824 = true := by decide +kernel

theorem slice0815 : slice 815 10 = [cellAt 815, cellAt 816, cellAt 817, cellAt 818, cellAt 819, cellAt 820, cellAt 821, cellAt 822, cellAt 823, cellAt 824] := by decide +kernel

theorem batch0815_ok : checkAll pa19 (slice 815 10) breaks0815 = true := by
  rw [slice0815]
  simp only [breaks0815, checkAll, c0815, c0816, c0817, c0818, c0819, c0820, c0821, c0822, c0823, c0824, Bool.and_self]

theorem batch0815 : ∀ c ∈ slice 815 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0815_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0815
