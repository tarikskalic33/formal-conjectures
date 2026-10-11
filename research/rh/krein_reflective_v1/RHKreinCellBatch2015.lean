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

/-! Serialized cells 2015 to 2024: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b2015 : List ℚ := [126075/512, 63075/256]
def b2016 : List ℚ := [126225/512, 31575/128]
def b2017 : List ℚ := [63225/256]
def b2018 : List ℚ := [15825/64]
def b2019 : List ℚ := [63375/256]
def b2020 : List ℚ := [31725/128]
def b2021 : List ℚ := [63525/256]
def b2022 : List ℚ := [3975/16]
def b2023 : List ℚ := [63675/256]
def b2024 : List ℚ := [31875/128]

def breaks2015 : List (List ℚ) := [b2015, b2016, b2017, b2018, b2019, b2020, b2021, b2022, b2023, b2024]

theorem c2015 : checkCell pa19 (cellAt 2015) b2015 = true := by decide +kernel

theorem c2016 : checkCell pa19 (cellAt 2016) b2016 = true := by decide +kernel

theorem c2017 : checkCell pa19 (cellAt 2017) b2017 = true := by decide +kernel

theorem c2018 : checkCell pa19 (cellAt 2018) b2018 = true := by decide +kernel

theorem c2019 : checkCell pa19 (cellAt 2019) b2019 = true := by decide +kernel

theorem c2020 : checkCell pa19 (cellAt 2020) b2020 = true := by decide +kernel

theorem c2021 : checkCell pa19 (cellAt 2021) b2021 = true := by decide +kernel

theorem c2022 : checkCell pa19 (cellAt 2022) b2022 = true := by decide +kernel

theorem c2023 : checkCell pa19 (cellAt 2023) b2023 = true := by decide +kernel

theorem c2024 : checkCell pa19 (cellAt 2024) b2024 = true := by decide +kernel

theorem slice2015 : slice 2015 10 = [cellAt 2015, cellAt 2016, cellAt 2017, cellAt 2018, cellAt 2019, cellAt 2020, cellAt 2021, cellAt 2022, cellAt 2023, cellAt 2024] := by decide +kernel

theorem batch2015_ok : checkAll pa19 (slice 2015 10) breaks2015 = true := by
  rw [slice2015]
  simp only [breaks2015, checkAll, c2015, c2016, c2017, c2018, c2019, c2020, c2021, c2022, c2023, c2024, Bool.and_self]

theorem batch2015 : ∀ c ∈ slice 2015 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch2015_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch2015
