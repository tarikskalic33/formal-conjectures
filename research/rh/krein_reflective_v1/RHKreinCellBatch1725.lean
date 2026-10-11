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

/-! Serialized cells 1725 to 1734: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b1725 : List ℚ := [41325/256]
def b1726 : List ℚ := [5175/32]
def b1727 : List ℚ := [41475/256]
def b1728 : List ℚ := [20775/128]
def b1729 : List ℚ := [41625/256]
def b1730 : List ℚ := [10425/64]
def b1731 : List ℚ := [41775/256]
def b1732 : List ℚ := [20925/128]
def b1733 : List ℚ := [41925/256]
def b1734 : List ℚ := [2625/16]

def breaks1725 : List (List ℚ) := [b1725, b1726, b1727, b1728, b1729, b1730, b1731, b1732, b1733, b1734]

theorem c1725 : checkCell pa19 (cellAt 1725) b1725 = true := by decide +kernel

theorem c1726 : checkCell pa19 (cellAt 1726) b1726 = true := by decide +kernel

theorem c1727 : checkCell pa19 (cellAt 1727) b1727 = true := by decide +kernel

theorem c1728 : checkCell pa19 (cellAt 1728) b1728 = true := by decide +kernel

theorem c1729 : checkCell pa19 (cellAt 1729) b1729 = true := by decide +kernel

theorem c1730 : checkCell pa19 (cellAt 1730) b1730 = true := by decide +kernel

theorem c1731 : checkCell pa19 (cellAt 1731) b1731 = true := by decide +kernel

theorem c1732 : checkCell pa19 (cellAt 1732) b1732 = true := by decide +kernel

theorem c1733 : checkCell pa19 (cellAt 1733) b1733 = true := by decide +kernel

theorem c1734 : checkCell pa19 (cellAt 1734) b1734 = true := by decide +kernel

theorem slice1725 : slice 1725 10 = [cellAt 1725, cellAt 1726, cellAt 1727, cellAt 1728, cellAt 1729, cellAt 1730, cellAt 1731, cellAt 1732, cellAt 1733, cellAt 1734] := by decide +kernel

theorem batch1725_ok : checkAll pa19 (slice 1725 10) breaks1725 = true := by
  rw [slice1725]
  simp only [breaks1725, checkAll, c1725, c1726, c1727, c1728, c1729, c1730, c1731, c1732, c1733, c1734, Bool.and_self]

theorem batch1725 : ∀ c ∈ slice 1725 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch1725_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch1725
