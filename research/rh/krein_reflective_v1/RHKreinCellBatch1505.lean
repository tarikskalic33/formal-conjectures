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

/-! Serialized cells 1505 to 1514: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1505 : List ℚ := [24825/256]
def b1506 : List ℚ := [6225/64]
def b1507 : List ℚ := [24975/256]
def b1508 : List ℚ := [12525/128]
def b1509 : List ℚ := [25125/256]
def b1510 : List ℚ := [1575/16]
def b1511 : List ℚ := [25275/256]
def b1512 : List ℚ := [12675/128]
def b1513 : List ℚ := [25425/256]
def b1514 : List ℚ := [6375/64]

def breaks1505 : List (List ℚ) := [b1505, b1506, b1507, b1508, b1509, b1510, b1511, b1512, b1513, b1514]

theorem c1505 : checkCell pa19 (cellAt 1505) b1505 = true := by decide +kernel

theorem c1506 : checkCell pa19 (cellAt 1506) b1506 = true := by decide +kernel

theorem c1507 : checkCell pa19 (cellAt 1507) b1507 = true := by decide +kernel

theorem c1508 : checkCell pa19 (cellAt 1508) b1508 = true := by decide +kernel

theorem c1509 : checkCell pa19 (cellAt 1509) b1509 = true := by decide +kernel

theorem c1510 : checkCell pa19 (cellAt 1510) b1510 = true := by decide +kernel

theorem c1511 : checkCell pa19 (cellAt 1511) b1511 = true := by decide +kernel

theorem c1512 : checkCell pa19 (cellAt 1512) b1512 = true := by decide +kernel

theorem c1513 : checkCell pa19 (cellAt 1513) b1513 = true := by decide +kernel

theorem c1514 : checkCell pa19 (cellAt 1514) b1514 = true := by decide +kernel

theorem slice1505 : slice 1505 10 = [cellAt 1505, cellAt 1506, cellAt 1507, cellAt 1508, cellAt 1509, cellAt 1510, cellAt 1511, cellAt 1512, cellAt 1513, cellAt 1514] := by decide +kernel

theorem batch1505_ok : checkAll pa19 (slice 1505 10) breaks1505 = true := by
  rw [slice1505]
  simp only [breaks1505, checkAll, c1505, c1506, c1507, c1508, c1509, c1510, c1511, c1512, c1513, c1514, Bool.and_self]

theorem batch1505 : ∀ c ∈ slice 1505 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1505_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1505
