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

/-! Serialized cells 1885 to 1894: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1885 : List ℚ := [53325/256]
def b1886 : List ℚ := [6675/32]
def b1887 : List ℚ := [53475/256]
def b1888 : List ℚ := [26775/128]
def b1889 : List ℚ := [53625/256]
def b1890 : List ℚ := [13425/64]
def b1891 : List ℚ := [53775/256]
def b1892 : List ℚ := [26925/128]
def b1893 : List ℚ := [53925/256]
def b1894 : List ℚ := [3375/16]

def breaks1885 : List (List ℚ) := [b1885, b1886, b1887, b1888, b1889, b1890, b1891, b1892, b1893, b1894]

theorem c1885 : checkCell pa19 (cellAt 1885) b1885 = true := by decide +kernel

theorem c1886 : checkCell pa19 (cellAt 1886) b1886 = true := by decide +kernel

theorem c1887 : checkCell pa19 (cellAt 1887) b1887 = true := by decide +kernel

theorem c1888 : checkCell pa19 (cellAt 1888) b1888 = true := by decide +kernel

theorem c1889 : checkCell pa19 (cellAt 1889) b1889 = true := by decide +kernel

theorem c1890 : checkCell pa19 (cellAt 1890) b1890 = true := by decide +kernel

theorem c1891 : checkCell pa19 (cellAt 1891) b1891 = true := by decide +kernel

theorem c1892 : checkCell pa19 (cellAt 1892) b1892 = true := by decide +kernel

theorem c1893 : checkCell pa19 (cellAt 1893) b1893 = true := by decide +kernel

theorem c1894 : checkCell pa19 (cellAt 1894) b1894 = true := by decide +kernel

theorem slice1885 : slice 1885 10 = [cellAt 1885, cellAt 1886, cellAt 1887, cellAt 1888, cellAt 1889, cellAt 1890, cellAt 1891, cellAt 1892, cellAt 1893, cellAt 1894] := by decide +kernel

theorem batch1885_ok : checkAll pa19 (slice 1885 10) breaks1885 = true := by
  rw [slice1885]
  simp only [breaks1885, checkAll, c1885, c1886, c1887, c1888, c1889, c1890, c1891, c1892, c1893, c1894, Bool.and_self]

theorem batch1885 : ∀ c ∈ slice 1885 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1885_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1885
