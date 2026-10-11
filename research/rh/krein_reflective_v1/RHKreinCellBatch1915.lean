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

/-! Serialized cells 1915 to 1924: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1915 : List ℚ := [55575/256]
def b1916 : List ℚ := [27825/128]
def b1917 : List ℚ := [55725/256]
def b1918 : List ℚ := [6975/32]
def b1919 : List ℚ := [55875/256]
def b1920 : List ℚ := [27975/128]
def b1921 : List ℚ := [56025/256]
def b1922 : List ℚ := [14025/64]
def b1923 : List ℚ := [56175/256]
def b1924 : List ℚ := [28125/128]

def breaks1915 : List (List ℚ) := [b1915, b1916, b1917, b1918, b1919, b1920, b1921, b1922, b1923, b1924]

theorem c1915 : checkCell pa19 (cellAt 1915) b1915 = true := by decide +kernel

theorem c1916 : checkCell pa19 (cellAt 1916) b1916 = true := by decide +kernel

theorem c1917 : checkCell pa19 (cellAt 1917) b1917 = true := by decide +kernel

theorem c1918 : checkCell pa19 (cellAt 1918) b1918 = true := by decide +kernel

theorem c1919 : checkCell pa19 (cellAt 1919) b1919 = true := by decide +kernel

theorem c1920 : checkCell pa19 (cellAt 1920) b1920 = true := by decide +kernel

theorem c1921 : checkCell pa19 (cellAt 1921) b1921 = true := by decide +kernel

theorem c1922 : checkCell pa19 (cellAt 1922) b1922 = true := by decide +kernel

theorem c1923 : checkCell pa19 (cellAt 1923) b1923 = true := by decide +kernel

theorem c1924 : checkCell pa19 (cellAt 1924) b1924 = true := by decide +kernel

theorem slice1915 : slice 1915 10 = [cellAt 1915, cellAt 1916, cellAt 1917, cellAt 1918, cellAt 1919, cellAt 1920, cellAt 1921, cellAt 1922, cellAt 1923, cellAt 1924] := by decide +kernel

theorem batch1915_ok : checkAll pa19 (slice 1915 10) breaks1915 = true := by
  rw [slice1915]
  simp only [breaks1915, checkAll, c1915, c1916, c1917, c1918, c1919, c1920, c1921, c1922, c1923, c1924, Bool.and_self]

theorem batch1915 : ∀ c ∈ slice 1915 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1915_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1915
