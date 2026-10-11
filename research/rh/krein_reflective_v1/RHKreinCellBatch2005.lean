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

/-! Serialized cells 2005 to 2014: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

def b2005 : List ℚ := [124575/512, 62325/256]
def b2006 : List ℚ := [124725/512, 975/4]
def b2007 : List ℚ := [124875/512, 62475/256]
def b2008 : List ℚ := [125025/512, 31275/128]
def b2009 : List ℚ := [125175/512, 62625/256]
def b2010 : List ℚ := [125325/512, 15675/64]
def b2011 : List ℚ := [125475/512, 62775/256]
def b2012 : List ℚ := [125625/512, 31425/128]
def b2013 : List ℚ := [125775/512, 62925/256]
def b2014 : List ℚ := [125925/512, 7875/32]

def breaks2005 : List (List ℚ) := [b2005, b2006, b2007, b2008, b2009, b2010, b2011, b2012, b2013, b2014]

theorem c2005 : checkCell pa19 (cellAt 2005) b2005 = true := by decide +kernel

theorem c2006 : checkCell pa19 (cellAt 2006) b2006 = true := by decide +kernel

theorem c2007 : checkCell pa19 (cellAt 2007) b2007 = true := by decide +kernel

theorem c2008 : checkCell pa19 (cellAt 2008) b2008 = true := by decide +kernel

theorem c2009 : checkCell pa19 (cellAt 2009) b2009 = true := by decide +kernel

theorem c2010 : checkCell pa19 (cellAt 2010) b2010 = true := by decide +kernel

theorem c2011 : checkCell pa19 (cellAt 2011) b2011 = true := by decide +kernel

theorem c2012 : checkCell pa19 (cellAt 2012) b2012 = true := by decide +kernel

theorem c2013 : checkCell pa19 (cellAt 2013) b2013 = true := by decide +kernel

theorem c2014 : checkCell pa19 (cellAt 2014) b2014 = true := by decide +kernel

theorem slice2005 : slice 2005 10 = [cellAt 2005, cellAt 2006, cellAt 2007, cellAt 2008, cellAt 2009, cellAt 2010, cellAt 2011, cellAt 2012, cellAt 2013, cellAt 2014] := by decide +kernel

theorem batch2005_ok : checkAll pa19 (slice 2005 10) breaks2005 = true := by
  rw [slice2005]
  simp only [breaks2005, checkAll, c2005, c2006, c2007, c2008, c2009, c2010, c2011, c2012, c2013, c2014, Bool.and_self]

theorem batch2005 : ∀ c ∈ slice 2005 10, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch2005_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch2005
