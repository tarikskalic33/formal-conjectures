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

/-! Serialized cells 1905 to 1914: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1905 : List ℚ := [54825/256]
def b1906 : List ℚ := [13725/64]
def b1907 : List ℚ := [54975/256]
def b1908 : List ℚ := [27525/128]
def b1909 : List ℚ := [55125/256]
def b1910 : List ℚ := [1725/8]
def b1911 : List ℚ := [55275/256]
def b1912 : List ℚ := [27675/128]
def b1913 : List ℚ := [55425/256]
def b1914 : List ℚ := [13875/64]

def breaks1905 : List (List ℚ) := [b1905, b1906, b1907, b1908, b1909, b1910, b1911, b1912, b1913, b1914]

theorem c1905 : checkCell pa19 (cellAt 1905) b1905 = true := by decide +kernel

theorem c1906 : checkCell pa19 (cellAt 1906) b1906 = true := by decide +kernel

theorem c1907 : checkCell pa19 (cellAt 1907) b1907 = true := by decide +kernel

theorem c1908 : checkCell pa19 (cellAt 1908) b1908 = true := by decide +kernel

theorem c1909 : checkCell pa19 (cellAt 1909) b1909 = true := by decide +kernel

theorem c1910 : checkCell pa19 (cellAt 1910) b1910 = true := by decide +kernel

theorem c1911 : checkCell pa19 (cellAt 1911) b1911 = true := by decide +kernel

theorem c1912 : checkCell pa19 (cellAt 1912) b1912 = true := by decide +kernel

theorem c1913 : checkCell pa19 (cellAt 1913) b1913 = true := by decide +kernel

theorem c1914 : checkCell pa19 (cellAt 1914) b1914 = true := by decide +kernel

theorem slice1905 : slice 1905 10 = [cellAt 1905, cellAt 1906, cellAt 1907, cellAt 1908, cellAt 1909, cellAt 1910, cellAt 1911, cellAt 1912, cellAt 1913, cellAt 1914] := by decide +kernel

theorem batch1905_ok : checkAll pa19 (slice 1905 10) breaks1905 = true := by
  rw [slice1905]
  simp only [breaks1905, checkAll, c1905, c1906, c1907, c1908, c1909, c1910, c1911, c1912, c1913, c1914, Bool.and_self]

theorem batch1905 : ∀ c ∈ slice 1905 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1905_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1905
