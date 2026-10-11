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

/-! Serialized cells 1935 to 1944: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1935 : List ℚ := [57075/256]
def b1936 : List ℚ := [28575/128]
def b1937 : List ℚ := [57225/256]
def b1938 : List ℚ := [14325/64]
def b1939 : List ℚ := [57375/256]
def b1940 : List ℚ := [28725/128]
def b1941 : List ℚ := [57525/256]
def b1942 : List ℚ := [225]
def b1943 : List ℚ := [57675/256]
def b1944 : List ℚ := [28875/128]

def breaks1935 : List (List ℚ) := [b1935, b1936, b1937, b1938, b1939, b1940, b1941, b1942, b1943, b1944]

theorem c1935 : checkCell pa19 (cellAt 1935) b1935 = true := by decide +kernel

theorem c1936 : checkCell pa19 (cellAt 1936) b1936 = true := by decide +kernel

theorem c1937 : checkCell pa19 (cellAt 1937) b1937 = true := by decide +kernel

theorem c1938 : checkCell pa19 (cellAt 1938) b1938 = true := by decide +kernel

theorem c1939 : checkCell pa19 (cellAt 1939) b1939 = true := by decide +kernel

theorem c1940 : checkCell pa19 (cellAt 1940) b1940 = true := by decide +kernel

theorem c1941 : checkCell pa19 (cellAt 1941) b1941 = true := by decide +kernel

theorem c1942 : checkCell pa19 (cellAt 1942) b1942 = true := by decide +kernel

theorem c1943 : checkCell pa19 (cellAt 1943) b1943 = true := by decide +kernel

theorem c1944 : checkCell pa19 (cellAt 1944) b1944 = true := by decide +kernel

theorem slice1935 : slice 1935 10 = [cellAt 1935, cellAt 1936, cellAt 1937, cellAt 1938, cellAt 1939, cellAt 1940, cellAt 1941, cellAt 1942, cellAt 1943, cellAt 1944] := by decide +kernel

theorem batch1935_ok : checkAll pa19 (slice 1935 10) breaks1935 = true := by
  rw [slice1935]
  simp only [breaks1935, checkAll, c1935, c1936, c1937, c1938, c1939, c1940, c1941, c1942, c1943, c1944, Bool.and_self]

theorem batch1935 : ∀ c ∈ slice 1935 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1935_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1935
