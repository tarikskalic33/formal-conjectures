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

/-! Serialized cells 1895 to 1904: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1895 : List ℚ := [54075/256]
def b1896 : List ℚ := [27075/128]
def b1897 : List ℚ := [54225/256]
def b1898 : List ℚ := [13575/64]
def b1899 : List ℚ := [54375/256]
def b1900 : List ℚ := [27225/128]
def b1901 : List ℚ := [54525/256]
def b1902 : List ℚ := [6825/32]
def b1903 : List ℚ := [54675/256]
def b1904 : List ℚ := [27375/128]

def breaks1895 : List (List ℚ) := [b1895, b1896, b1897, b1898, b1899, b1900, b1901, b1902, b1903, b1904]

theorem c1895 : checkCell pa19 (cellAt 1895) b1895 = true := by decide +kernel

theorem c1896 : checkCell pa19 (cellAt 1896) b1896 = true := by decide +kernel

theorem c1897 : checkCell pa19 (cellAt 1897) b1897 = true := by decide +kernel

theorem c1898 : checkCell pa19 (cellAt 1898) b1898 = true := by decide +kernel

theorem c1899 : checkCell pa19 (cellAt 1899) b1899 = true := by decide +kernel

theorem c1900 : checkCell pa19 (cellAt 1900) b1900 = true := by decide +kernel

theorem c1901 : checkCell pa19 (cellAt 1901) b1901 = true := by decide +kernel

theorem c1902 : checkCell pa19 (cellAt 1902) b1902 = true := by decide +kernel

theorem c1903 : checkCell pa19 (cellAt 1903) b1903 = true := by decide +kernel

theorem c1904 : checkCell pa19 (cellAt 1904) b1904 = true := by decide +kernel

theorem slice1895 : slice 1895 10 = [cellAt 1895, cellAt 1896, cellAt 1897, cellAt 1898, cellAt 1899, cellAt 1900, cellAt 1901, cellAt 1902, cellAt 1903, cellAt 1904] := by decide +kernel

theorem batch1895_ok : checkAll pa19 (slice 1895 10) breaks1895 = true := by
  rw [slice1895]
  simp only [breaks1895, checkAll, c1895, c1896, c1897, c1898, c1899, c1900, c1901, c1902, c1903, c1904, Bool.and_self]

theorem batch1895 : ∀ c ∈ slice 1895 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1895_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1895
