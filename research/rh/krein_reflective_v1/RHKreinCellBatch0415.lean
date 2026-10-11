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

/-! Serialized cells 415 to 424: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b0415 : List ℚ := [32625/32768]
def b0416 : List ℚ := [8175/8192]
def b0417 : List ℚ := [32775/32768]
def b0418 : List ℚ := [16425/16384]
def b0419 : List ℚ := [32925/32768]
def b0420 : List ℚ := [4125/4096]
def b0421 : List ℚ := [33075/32768]
def b0422 : List ℚ := [16575/16384]
def b0423 : List ℚ := [33225/32768]
def b0424 : List ℚ := [8325/8192]

def breaks0415 : List (List ℚ) := [b0415, b0416, b0417, b0418, b0419, b0420, b0421, b0422, b0423, b0424]

theorem c0415 : checkCell pa19 (cellAt 415) b0415 = true := by decide +kernel

theorem c0416 : checkCell pa19 (cellAt 416) b0416 = true := by decide +kernel

theorem c0417 : checkCell pa19 (cellAt 417) b0417 = true := by decide +kernel

theorem c0418 : checkCell pa19 (cellAt 418) b0418 = true := by decide +kernel

theorem c0419 : checkCell pa19 (cellAt 419) b0419 = true := by decide +kernel

theorem c0420 : checkCell pa19 (cellAt 420) b0420 = true := by decide +kernel

theorem c0421 : checkCell pa19 (cellAt 421) b0421 = true := by decide +kernel

theorem c0422 : checkCell pa19 (cellAt 422) b0422 = true := by decide +kernel

theorem c0423 : checkCell pa19 (cellAt 423) b0423 = true := by decide +kernel

theorem c0424 : checkCell pa19 (cellAt 424) b0424 = true := by decide +kernel

theorem slice0415 : slice 415 10 = [cellAt 415, cellAt 416, cellAt 417, cellAt 418, cellAt 419, cellAt 420, cellAt 421, cellAt 422, cellAt 423, cellAt 424] := by decide +kernel

theorem batch0415_ok : checkAll pa19 (slice 415 10) breaks0415 = true := by
  rw [slice0415]
  simp only [breaks0415, checkAll, c0415, c0416, c0417, c0418, c0419, c0420, c0421, c0422, c0423, c0424, Bool.and_self]

theorem batch0415 : ∀ c ∈ slice 415 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch0415_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch0415
