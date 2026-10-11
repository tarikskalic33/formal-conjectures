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

/-! Serialized cells 595 to 604: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0595 : List ℚ := [25575/16384]
def b0596 : List ℚ := [12825/8192]
def b0597 : List ℚ := [25725/16384]
def b0598 : List ℚ := [3225/2048]
def b0599 : List ℚ := [25875/16384]
def b0600 : List ℚ := [12975/8192]
def b0601 : List ℚ := [26025/16384]
def b0602 : List ℚ := [6525/4096]
def b0603 : List ℚ := [26175/16384]
def b0604 : List ℚ := [13125/8192]

def breaks0595 : List (List ℚ) := [b0595, b0596, b0597, b0598, b0599, b0600, b0601, b0602, b0603, b0604]

theorem c0595 : checkCell pa19 (cellAt 595) b0595 = true := by decide +kernel

theorem c0596 : checkCell pa19 (cellAt 596) b0596 = true := by decide +kernel

theorem c0597 : checkCell pa19 (cellAt 597) b0597 = true := by decide +kernel

theorem c0598 : checkCell pa19 (cellAt 598) b0598 = true := by decide +kernel

theorem c0599 : checkCell pa19 (cellAt 599) b0599 = true := by decide +kernel

theorem c0600 : checkCell pa19 (cellAt 600) b0600 = true := by decide +kernel

theorem c0601 : checkCell pa19 (cellAt 601) b0601 = true := by decide +kernel

theorem c0602 : checkCell pa19 (cellAt 602) b0602 = true := by decide +kernel

theorem c0603 : checkCell pa19 (cellAt 603) b0603 = true := by decide +kernel

theorem c0604 : checkCell pa19 (cellAt 604) b0604 = true := by decide +kernel

theorem slice0595 : slice 595 10 = [cellAt 595, cellAt 596, cellAt 597, cellAt 598, cellAt 599, cellAt 600, cellAt 601, cellAt 602, cellAt 603, cellAt 604] := by decide +kernel

theorem batch0595_ok : checkAll pa19 (slice 595 10) breaks0595 = true := by
  rw [slice0595]
  simp only [breaks0595, checkAll, c0595, c0596, c0597, c0598, c0599, c0600, c0601, c0602, c0603, c0604, Bool.and_self]

theorem batch0595 : ∀ c ∈ slice 595 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0595_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0595
