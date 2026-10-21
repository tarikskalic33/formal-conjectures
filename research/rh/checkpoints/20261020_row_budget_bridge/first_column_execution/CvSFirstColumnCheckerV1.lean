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
import CvSColumnEnvelopeV1
import RowBudgetListCell0Pilot
namespace AEGIS.CvSFirstColumnCheckerV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSIntervalMatrixProductV1
open AEGIS.CvSColumnEnvelopeV1 AEGIS.CvSListIntervalDotV1
open AEGIS.RowBudgetStagedDotPilot AEGIS.RowBudgetListCell0Pilot

structure Entry where
  row : Fin 139
  q : Iv
  a : List Iv
  da : List Iv
  u : List Iv
  target : Iv

def wellFormed (e : Entry) : Prop :=
  e.a.length = 141 ∧ e.da.length = 141 ∧ e.u.length = 301 ∧
    ∀ k : Fin 141, (T.getD k.val ⟨0, 0⟩).mul 96
      (e.a.getD k.val ⟨0, 0⟩) = e.da.getD k.val ⟨0, 0⟩

instance (e : Entry) : Decidable (wellFormed e) := inferInstanceAs (Decidable
  (e.a.length = 141 ∧ e.da.length = 141 ∧ e.u.length = 301 ∧
    ∀ k : Fin 141, (T.getD k.val ⟨0, 0⟩).mul 96
      (e.a.getD k.val ⟨0, 0⟩) = e.da.getD k.val ⟨0, 0⟩))

def check (e : Entry) : Bool := decide (wellFormed e) && contains e.target
  (downscale 16 (columnValue 96 e.q e.a e.da e.u Z0 GX0 GDX0 LP2))

def originalEntry (e : Entry) : Iv := downscale 16
  (AEGIS.CvSRowBudgetEnvelopeV1.envelope 96 (fun (_ _ : Fin 2) => e.q)
    (twoColumns (n := 141) e.a X0)
    (fun k l : Fin 141 => (G.getD k.val []).getD l.val ⟨0, 0⟩)
    (fun k : Fin 141 => T.getD k.val ⟨0, 0⟩)
    (twoColumns (n := 301) e.u Z0) LP2 0 1)

/-- A checked mixed entry encloses the unchanged finite envelope expression. -/
theorem check_sound (e : Entry) (h : check e = true) :
    contains e.target (originalEntry e) = true := by
  have hh := Bool.and_eq_true_iff.mp h
  have hw : wellFormed e := of_decide_eq_true hh.1
  unfold originalEntry
  rw [envelope_pair_eq 96 e.q LP2 e.a X0 e.da DX0 T e.u Z0 G
    hw.1 X_length hw.2.1 DX_length hw.2.2.1 Z_length G_length G_rows
    hw.2.2.2 weighted_column_exact, gram_source_exact, gram_weighted_exact]
  exact hh.2

end AEGIS.CvSFirstColumnCheckerV1
#print axioms AEGIS.CvSFirstColumnCheckerV1.check_sound
#check @AEGIS.CvSFirstColumnCheckerV1.check_sound
