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

/-! Serialized cells 1995 to 2004: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1995 : List ℚ := [61575/256]
def b1996 : List ℚ := [30825/128]
def b1997 : List ℚ := [61725/256]
def b1998 : List ℚ := [7725/32]
def b1999 : List ℚ := [61875/256]
def b2000 : List ℚ := [30975/128]
def b2001 : List ℚ := [62025/256]
def b2002 : List ℚ := [15525/64]
def b2003 : List ℚ := [62175/256]
def b2004 : List ℚ := [31125/128]

def breaks1995 : List (List ℚ) := [b1995, b1996, b1997, b1998, b1999, b2000, b2001, b2002, b2003, b2004]

theorem c1995 : checkCell pa19 (cellAt 1995) b1995 = true := by decide +kernel

theorem c1996 : checkCell pa19 (cellAt 1996) b1996 = true := by decide +kernel

theorem c1997 : checkCell pa19 (cellAt 1997) b1997 = true := by decide +kernel

theorem c1998 : checkCell pa19 (cellAt 1998) b1998 = true := by decide +kernel

theorem c1999 : checkCell pa19 (cellAt 1999) b1999 = true := by decide +kernel

theorem c2000 : checkCell pa19 (cellAt 2000) b2000 = true := by decide +kernel

theorem c2001 : checkCell pa19 (cellAt 2001) b2001 = true := by decide +kernel

theorem c2002 : checkCell pa19 (cellAt 2002) b2002 = true := by decide +kernel

theorem c2003 : checkCell pa19 (cellAt 2003) b2003 = true := by decide +kernel

theorem c2004 : checkCell pa19 (cellAt 2004) b2004 = true := by decide +kernel

theorem slice1995 : slice 1995 10 = [cellAt 1995, cellAt 1996, cellAt 1997, cellAt 1998, cellAt 1999, cellAt 2000, cellAt 2001, cellAt 2002, cellAt 2003, cellAt 2004] := by decide +kernel

theorem batch1995_ok : checkAll pa19 (slice 1995 10) breaks1995 = true := by
  rw [slice1995]
  simp only [breaks1995, checkAll, c1995, c1996, c1997, c1998, c1999, c2000, c2001, c2002, c2003, c2004, Bool.and_self]

theorem batch1995 : ∀ c ∈ slice 1995 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1995_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1995
