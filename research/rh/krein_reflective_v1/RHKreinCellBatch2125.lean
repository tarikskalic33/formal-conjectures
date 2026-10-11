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

/-! Serialized cells 2125 to 2134: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b2125 : List ℚ := [71325/256]
def b2126 : List ℚ := [8925/32]
def b2127 : List ℚ := [71475/256]
def b2128 : List ℚ := [35775/128]
def b2129 : List ℚ := [71625/256]
def b2130 : List ℚ := [17925/64]
def b2131 : List ℚ := [71775/256]
def b2132 : List ℚ := [35925/128]
def b2133 : List ℚ := [143775/512, 71925/256]
def b2134 : List ℚ := [1125/4]

def breaks2125 : List (List ℚ) := [b2125, b2126, b2127, b2128, b2129, b2130, b2131, b2132, b2133, b2134]

theorem c2125 : checkCell pa19 (cellAt 2125) b2125 = true := by decide +kernel

theorem c2126 : checkCell pa19 (cellAt 2126) b2126 = true := by decide +kernel

theorem c2127 : checkCell pa19 (cellAt 2127) b2127 = true := by decide +kernel

theorem c2128 : checkCell pa19 (cellAt 2128) b2128 = true := by decide +kernel

theorem c2129 : checkCell pa19 (cellAt 2129) b2129 = true := by decide +kernel

theorem c2130 : checkCell pa19 (cellAt 2130) b2130 = true := by decide +kernel

theorem c2131 : checkCell pa19 (cellAt 2131) b2131 = true := by decide +kernel

theorem c2132 : checkCell pa19 (cellAt 2132) b2132 = true := by decide +kernel

theorem c2133 : checkCell pa19 (cellAt 2133) b2133 = true := by decide +kernel

theorem c2134 : checkCell pa19 (cellAt 2134) b2134 = true := by decide +kernel

theorem slice2125 : slice 2125 10 = [cellAt 2125, cellAt 2126, cellAt 2127, cellAt 2128, cellAt 2129, cellAt 2130, cellAt 2131, cellAt 2132, cellAt 2133, cellAt 2134] := by decide +kernel

theorem batch2125_ok : checkAll pa19 (slice 2125 10) breaks2125 = true := by
  rw [slice2125]
  simp only [breaks2125, checkAll, c2125, c2126, c2127, c2128, c2129, c2130, c2131, c2132, c2133, c2134, Bool.and_self]

theorem batch2125 : ∀ c ∈ slice 2125 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch2125_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch2125
