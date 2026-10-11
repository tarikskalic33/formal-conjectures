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

/-! Serialized cells 1945 to 1954: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1945 : List ℚ := [57825/256]
def b1946 : List ℚ := [14475/64]
def b1947 : List ℚ := [57975/256]
def b1948 : List ℚ := [29025/128]
def b1949 : List ℚ := [58125/256]
def b1950 : List ℚ := [7275/32]
def b1951 : List ℚ := [58275/256]
def b1952 : List ℚ := [29175/128]
def b1953 : List ℚ := [58425/256]
def b1954 : List ℚ := [14625/64]

def breaks1945 : List (List ℚ) := [b1945, b1946, b1947, b1948, b1949, b1950, b1951, b1952, b1953, b1954]

theorem c1945 : checkCell pa19 (cellAt 1945) b1945 = true := by decide +kernel

theorem c1946 : checkCell pa19 (cellAt 1946) b1946 = true := by decide +kernel

theorem c1947 : checkCell pa19 (cellAt 1947) b1947 = true := by decide +kernel

theorem c1948 : checkCell pa19 (cellAt 1948) b1948 = true := by decide +kernel

theorem c1949 : checkCell pa19 (cellAt 1949) b1949 = true := by decide +kernel

theorem c1950 : checkCell pa19 (cellAt 1950) b1950 = true := by decide +kernel

theorem c1951 : checkCell pa19 (cellAt 1951) b1951 = true := by decide +kernel

theorem c1952 : checkCell pa19 (cellAt 1952) b1952 = true := by decide +kernel

theorem c1953 : checkCell pa19 (cellAt 1953) b1953 = true := by decide +kernel

theorem c1954 : checkCell pa19 (cellAt 1954) b1954 = true := by decide +kernel

theorem slice1945 : slice 1945 10 = [cellAt 1945, cellAt 1946, cellAt 1947, cellAt 1948, cellAt 1949, cellAt 1950, cellAt 1951, cellAt 1952, cellAt 1953, cellAt 1954] := by decide +kernel

theorem batch1945_ok : checkAll pa19 (slice 1945 10) breaks1945 = true := by
  rw [slice1945]
  simp only [breaks1945, checkAll, c1945, c1946, c1947, c1948, c1949, c1950, c1951, c1952, c1953, c1954, Bool.and_self]

theorem batch1945 : ∀ c ∈ slice 1945 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1945_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1945
