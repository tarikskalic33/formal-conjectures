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

/-! Serialized cells 925 to 934: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0925 : List ℚ := [16425/2048]
def b0926 : List ℚ := [4125/512]
def b0927 : List ℚ := [16575/2048]
def b0928 : List ℚ := [8325/1024]
def b0929 : List ℚ := [16725/2048]
def b0930 : List ℚ := [525/64]
def b0931 : List ℚ := [16875/2048]
def b0932 : List ℚ := [8475/1024]
def b0933 : List ℚ := [17025/2048]
def b0934 : List ℚ := [4275/512]

def breaks0925 : List (List ℚ) := [b0925, b0926, b0927, b0928, b0929, b0930, b0931, b0932, b0933, b0934]

theorem c0925 : checkCell pa19 (cellAt 925) b0925 = true := by decide +kernel

theorem c0926 : checkCell pa19 (cellAt 926) b0926 = true := by decide +kernel

theorem c0927 : checkCell pa19 (cellAt 927) b0927 = true := by decide +kernel

theorem c0928 : checkCell pa19 (cellAt 928) b0928 = true := by decide +kernel

theorem c0929 : checkCell pa19 (cellAt 929) b0929 = true := by decide +kernel

theorem c0930 : checkCell pa19 (cellAt 930) b0930 = true := by decide +kernel

theorem c0931 : checkCell pa19 (cellAt 931) b0931 = true := by decide +kernel

theorem c0932 : checkCell pa19 (cellAt 932) b0932 = true := by decide +kernel

theorem c0933 : checkCell pa19 (cellAt 933) b0933 = true := by decide +kernel

theorem c0934 : checkCell pa19 (cellAt 934) b0934 = true := by decide +kernel

theorem slice0925 : slice 925 10 = [cellAt 925, cellAt 926, cellAt 927, cellAt 928, cellAt 929, cellAt 930, cellAt 931, cellAt 932, cellAt 933, cellAt 934] := by decide +kernel

theorem batch0925_ok : checkAll pa19 (slice 925 10) breaks0925 = true := by
  rw [slice0925]
  simp only [breaks0925, checkAll, c0925, c0926, c0927, c0928, c0929, c0930, c0931, c0932, c0933, c0934, Bool.and_self]

theorem batch0925 : ∀ c ∈ slice 925 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0925_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0925
