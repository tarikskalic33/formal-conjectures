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

/-! Serialized cells 1925 to 1934: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1925 : List ℚ := [56325/256]
def b1926 : List ℚ := [3525/16]
def b1927 : List ℚ := [56475/256]
def b1928 : List ℚ := [28275/128]
def b1929 : List ℚ := [56625/256]
def b1930 : List ℚ := [14175/64]
def b1931 : List ℚ := [56775/256]
def b1932 : List ℚ := [28425/128]
def b1933 : List ℚ := [56925/256]
def b1934 : List ℚ := [7125/32]

def breaks1925 : List (List ℚ) := [b1925, b1926, b1927, b1928, b1929, b1930, b1931, b1932, b1933, b1934]

theorem c1925 : checkCell pa19 (cellAt 1925) b1925 = true := by decide +kernel

theorem c1926 : checkCell pa19 (cellAt 1926) b1926 = true := by decide +kernel

theorem c1927 : checkCell pa19 (cellAt 1927) b1927 = true := by decide +kernel

theorem c1928 : checkCell pa19 (cellAt 1928) b1928 = true := by decide +kernel

theorem c1929 : checkCell pa19 (cellAt 1929) b1929 = true := by decide +kernel

theorem c1930 : checkCell pa19 (cellAt 1930) b1930 = true := by decide +kernel

theorem c1931 : checkCell pa19 (cellAt 1931) b1931 = true := by decide +kernel

theorem c1932 : checkCell pa19 (cellAt 1932) b1932 = true := by decide +kernel

theorem c1933 : checkCell pa19 (cellAt 1933) b1933 = true := by decide +kernel

theorem c1934 : checkCell pa19 (cellAt 1934) b1934 = true := by decide +kernel

theorem slice1925 : slice 1925 10 = [cellAt 1925, cellAt 1926, cellAt 1927, cellAt 1928, cellAt 1929, cellAt 1930, cellAt 1931, cellAt 1932, cellAt 1933, cellAt 1934] := by decide +kernel

theorem batch1925_ok : checkAll pa19 (slice 1925 10) breaks1925 = true := by
  rw [slice1925]
  simp only [breaks1925, checkAll, c1925, c1926, c1927, c1928, c1929, c1930, c1931, c1932, c1933, c1934, Bool.and_self]

theorem batch1925 : ∀ c ∈ slice 1925 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1925_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1925
