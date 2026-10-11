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

/-! Serialized cells 935 to 944: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0935 : List ℚ := [17175/2048]
def b0936 : List ℚ := [8625/1024]
def b0937 : List ℚ := [17325/2048]
def b0938 : List ℚ := [2175/256]
def b0939 : List ℚ := [17475/2048]
def b0940 : List ℚ := [8775/1024]
def b0941 : List ℚ := [17625/2048]
def b0942 : List ℚ := [4425/512]
def b0943 : List ℚ := [17775/2048]
def b0944 : List ℚ := [8925/1024]

def breaks0935 : List (List ℚ) := [b0935, b0936, b0937, b0938, b0939, b0940, b0941, b0942, b0943, b0944]

theorem c0935 : checkCell pa19 (cellAt 935) b0935 = true := by decide +kernel

theorem c0936 : checkCell pa19 (cellAt 936) b0936 = true := by decide +kernel

theorem c0937 : checkCell pa19 (cellAt 937) b0937 = true := by decide +kernel

theorem c0938 : checkCell pa19 (cellAt 938) b0938 = true := by decide +kernel

theorem c0939 : checkCell pa19 (cellAt 939) b0939 = true := by decide +kernel

theorem c0940 : checkCell pa19 (cellAt 940) b0940 = true := by decide +kernel

theorem c0941 : checkCell pa19 (cellAt 941) b0941 = true := by decide +kernel

theorem c0942 : checkCell pa19 (cellAt 942) b0942 = true := by decide +kernel

theorem c0943 : checkCell pa19 (cellAt 943) b0943 = true := by decide +kernel

theorem c0944 : checkCell pa19 (cellAt 944) b0944 = true := by decide +kernel

theorem slice0935 : slice 935 10 = [cellAt 935, cellAt 936, cellAt 937, cellAt 938, cellAt 939, cellAt 940, cellAt 941, cellAt 942, cellAt 943, cellAt 944] := by decide +kernel

theorem batch0935_ok : checkAll pa19 (slice 935 10) breaks0935 = true := by
  rw [slice0935]
  simp only [breaks0935, checkAll, c0935, c0936, c0937, c0938, c0939, c0940, c0941, c0942, c0943, c0944, Bool.and_self]

theorem batch0935 : ∀ c ∈ slice 935 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0935_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0935
