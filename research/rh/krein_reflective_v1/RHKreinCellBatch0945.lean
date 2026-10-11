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

/-! Serialized cells 945 to 954: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0945 : List ℚ := [17925/2048]
def b0946 : List ℚ := [1125/128]
def b0947 : List ℚ := [18075/2048]
def b0948 : List ℚ := [9075/1024]
def b0949 : List ℚ := [4575/512]
def b0950 : List ℚ := [9225/1024]
def b0951 : List ℚ := [2325/256]
def b0952 : List ℚ := [9375/1024]
def b0953 : List ℚ := [4725/512]
def b0954 : List ℚ := [9525/1024]

def breaks0945 : List (List ℚ) := [b0945, b0946, b0947, b0948, b0949, b0950, b0951, b0952, b0953, b0954]

theorem c0945 : checkCell pa19 (cellAt 945) b0945 = true := by decide +kernel

theorem c0946 : checkCell pa19 (cellAt 946) b0946 = true := by decide +kernel

theorem c0947 : checkCell pa19 (cellAt 947) b0947 = true := by decide +kernel

theorem c0948 : checkCell pa19 (cellAt 948) b0948 = true := by decide +kernel

theorem c0949 : checkCell pa19 (cellAt 949) b0949 = true := by decide +kernel

theorem c0950 : checkCell pa19 (cellAt 950) b0950 = true := by decide +kernel

theorem c0951 : checkCell pa19 (cellAt 951) b0951 = true := by decide +kernel

theorem c0952 : checkCell pa19 (cellAt 952) b0952 = true := by decide +kernel

theorem c0953 : checkCell pa19 (cellAt 953) b0953 = true := by decide +kernel

theorem c0954 : checkCell pa19 (cellAt 954) b0954 = true := by decide +kernel

theorem slice0945 : slice 945 10 = [cellAt 945, cellAt 946, cellAt 947, cellAt 948, cellAt 949, cellAt 950, cellAt 951, cellAt 952, cellAt 953, cellAt 954] := by decide +kernel

theorem batch0945_ok : checkAll pa19 (slice 945 10) breaks0945 = true := by
  rw [slice0945]
  simp only [breaks0945, checkAll, c0945, c0946, c0947, c0948, c0949, c0950, c0951, c0952, c0953, c0954, Bool.and_self]

theorem batch0945 : ∀ c ∈ slice 945 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0945_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0945
