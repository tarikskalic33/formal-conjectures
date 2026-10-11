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

/-! Serialized cells 1985 to 1994: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1985 : List ℚ := [121575/512, 60825/256]
def b1986 : List ℚ := [121725/512, 15225/64]
def b1987 : List ℚ := [60975/256]
def b1988 : List ℚ := [30525/128]
def b1989 : List ℚ := [61125/256]
def b1990 : List ℚ := [3825/16]
def b1991 : List ℚ := [61275/256]
def b1992 : List ℚ := [30675/128]
def b1993 : List ℚ := [61425/256]
def b1994 : List ℚ := [15375/64]

def breaks1985 : List (List ℚ) := [b1985, b1986, b1987, b1988, b1989, b1990, b1991, b1992, b1993, b1994]

theorem c1985 : checkCell pa19 (cellAt 1985) b1985 = true := by decide +kernel

theorem c1986 : checkCell pa19 (cellAt 1986) b1986 = true := by decide +kernel

theorem c1987 : checkCell pa19 (cellAt 1987) b1987 = true := by decide +kernel

theorem c1988 : checkCell pa19 (cellAt 1988) b1988 = true := by decide +kernel

theorem c1989 : checkCell pa19 (cellAt 1989) b1989 = true := by decide +kernel

theorem c1990 : checkCell pa19 (cellAt 1990) b1990 = true := by decide +kernel

theorem c1991 : checkCell pa19 (cellAt 1991) b1991 = true := by decide +kernel

theorem c1992 : checkCell pa19 (cellAt 1992) b1992 = true := by decide +kernel

theorem c1993 : checkCell pa19 (cellAt 1993) b1993 = true := by decide +kernel

theorem c1994 : checkCell pa19 (cellAt 1994) b1994 = true := by decide +kernel

theorem slice1985 : slice 1985 10 = [cellAt 1985, cellAt 1986, cellAt 1987, cellAt 1988, cellAt 1989, cellAt 1990, cellAt 1991, cellAt 1992, cellAt 1993, cellAt 1994] := by decide +kernel

theorem batch1985_ok : checkAll pa19 (slice 1985 10) breaks1985 = true := by
  rw [slice1985]
  simp only [breaks1985, checkAll, c1985, c1986, c1987, c1988, c1989, c1990, c1991, c1992, c1993, c1994, Bool.and_self]

theorem batch1985 : ∀ c ∈ slice 1985 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1985_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1985
