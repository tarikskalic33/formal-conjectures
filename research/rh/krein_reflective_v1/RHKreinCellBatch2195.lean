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

/-! Serialized cells 2195 to 2198: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b2195 : List ℚ := [76575/256]
def b2196 : List ℚ := [153225/512, 38325/128]
def b2197 : List ℚ := [153375/512, 76725/256]
def b2198 : List ℚ := [153525/512, 300]

def breaks2195 : List (List ℚ) := [b2195, b2196, b2197, b2198]

theorem c2195 : checkCell pa19 (cellAt 2195) b2195 = true := by decide +kernel

theorem c2196 : checkCell pa19 (cellAt 2196) b2196 = true := by decide +kernel

theorem c2197 : checkCell pa19 (cellAt 2197) b2197 = true := by decide +kernel

theorem c2198 : checkCell pa19 (cellAt 2198) b2198 = true := by decide +kernel

theorem slice2195 : slice 2195 4 = [cellAt 2195, cellAt 2196, cellAt 2197, cellAt 2198] := by decide +kernel

theorem batch2195_ok : checkAll pa19 (slice 2195 4) breaks2195 = true := by
  rw [slice2195]
  simp only [breaks2195, checkAll, c2195, c2196, c2197, c2198, Bool.and_self]

theorem batch2195 : ∀ c ∈ slice 2195 4, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch2195_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch2195
