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
/- All 139 entries of the first stored column; numeric source algorithm only. -/
import RowBudgetFirstColumnBatch0
import RowBudgetFirstColumnBatch1
import RowBudgetFirstColumnBatch2
import RowBudgetFirstColumnBatch3
import RowBudgetFirstColumnBatch4
import RowBudgetFirstColumnBatch5
import RowBudgetFirstColumnBatch6
import RowBudgetFirstColumnBatch7
import RowBudgetFirstColumnBatch8
import RowBudgetFirstColumnBatch9
import RowBudgetFirstColumnBatch10
import RowBudgetFirstColumnBatch11
import RowBudgetFirstColumnBatch12
import RowBudgetFirstColumnBatch13
namespace AEGIS.RowBudgetFirstColumnV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSIntervalMatrixProductV1
open AEGIS.CvSFirstColumnCheckerV1
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
def entries : List Entry := AEGIS.RowBudgetFirstColumnBatch0.entries ++ AEGIS.RowBudgetFirstColumnBatch1.entries ++ AEGIS.RowBudgetFirstColumnBatch2.entries ++ AEGIS.RowBudgetFirstColumnBatch3.entries ++ AEGIS.RowBudgetFirstColumnBatch4.entries ++ AEGIS.RowBudgetFirstColumnBatch5.entries ++ AEGIS.RowBudgetFirstColumnBatch6.entries ++ AEGIS.RowBudgetFirstColumnBatch7.entries ++ AEGIS.RowBudgetFirstColumnBatch8.entries ++ AEGIS.RowBudgetFirstColumnBatch9.entries ++ AEGIS.RowBudgetFirstColumnBatch10.entries ++ AEGIS.RowBudgetFirstColumnBatch11.entries ++ AEGIS.RowBudgetFirstColumnBatch12.entries ++ AEGIS.RowBudgetFirstColumnBatch13.entries
theorem checked : entries.all check = true := by
  simp only [entries, List.all_append, AEGIS.RowBudgetFirstColumnBatch0.checked, AEGIS.RowBudgetFirstColumnBatch1.checked, AEGIS.RowBudgetFirstColumnBatch2.checked, AEGIS.RowBudgetFirstColumnBatch3.checked, AEGIS.RowBudgetFirstColumnBatch4.checked, AEGIS.RowBudgetFirstColumnBatch5.checked, AEGIS.RowBudgetFirstColumnBatch6.checked, AEGIS.RowBudgetFirstColumnBatch7.checked, AEGIS.RowBudgetFirstColumnBatch8.checked, AEGIS.RowBudgetFirstColumnBatch9.checked, AEGIS.RowBudgetFirstColumnBatch10.checked, AEGIS.RowBudgetFirstColumnBatch11.checked, AEGIS.RowBudgetFirstColumnBatch12.checked, AEGIS.RowBudgetFirstColumnBatch13.checked, Bool.and_self]
theorem target_source : entries.all (fun e => decide (e.target = AEGIS.CvSPackedGramV1.Im AEGIS.CvSRelativeRowCertificateL12V1.intervals e.row.val 0)) = true := by
  simp only [entries, List.all_append, AEGIS.RowBudgetFirstColumnBatch0.target_source, AEGIS.RowBudgetFirstColumnBatch1.target_source, AEGIS.RowBudgetFirstColumnBatch2.target_source, AEGIS.RowBudgetFirstColumnBatch3.target_source, AEGIS.RowBudgetFirstColumnBatch4.target_source, AEGIS.RowBudgetFirstColumnBatch5.target_source, AEGIS.RowBudgetFirstColumnBatch6.target_source, AEGIS.RowBudgetFirstColumnBatch7.target_source, AEGIS.RowBudgetFirstColumnBatch8.target_source, AEGIS.RowBudgetFirstColumnBatch9.target_source, AEGIS.RowBudgetFirstColumnBatch10.target_source, AEGIS.RowBudgetFirstColumnBatch11.target_source, AEGIS.RowBudgetFirstColumnBatch12.target_source, AEGIS.RowBudgetFirstColumnBatch13.target_source, Bool.and_self]
theorem row_order : entries.map (fun e => e.row.val) = List.range 139 := by
  decide +kernel

/-- All 139 original target boxes contain their original first-column envelope entry. -/
theorem first_column_contains (e : Entry) (he : e ∈ entries) :
    contains (AEGIS.CvSPackedGramV1.Im
      AEGIS.CvSRelativeRowCertificateL12V1.intervals e.row.val 0) (originalEntry e) = true := by
  have hc : check e = true := List.all_eq_true.mp checked e he
  have ht : e.target = AEGIS.CvSPackedGramV1.Im
      AEGIS.CvSRelativeRowCertificateL12V1.intervals e.row.val 0 :=
    of_decide_eq_true (List.all_eq_true.mp target_source e he)
  rw [← ht]
  exact check_sound e hc

/-- Membership passes to the exact stored Q80 target with no widening assumption. -/
theorem first_column_mem (e : Entry) (he : e ∈ entries) {x : ℝ}
    (hx : (originalEntry e).Mem 80 x) :
    (AEGIS.CvSPackedGramV1.Im AEGIS.CvSRelativeRowCertificateL12V1.intervals e.row.val 0).Mem 80 x :=
  mem_of_contains 80 (first_column_contains e he) hx

/-- Every original row index occurs in the checked first-column list. -/
theorem all_rows_covered (i : Fin 139) : ∃ e ∈ entries, e.row = i := by
  have hi : i.val ∈ entries.map (fun e => e.row.val) := by
    rw [row_order]
    exact List.mem_range.mpr i.isLt
  obtain ⟨e, he, hrow⟩ := List.mem_map.mp hi
  exact ⟨e, he, Fin.ext hrow⟩

end AEGIS.RowBudgetFirstColumnV1
#print axioms AEGIS.RowBudgetFirstColumnV1.checked
#check @AEGIS.RowBudgetFirstColumnV1.checked
#print axioms AEGIS.RowBudgetFirstColumnV1.target_source
#check @AEGIS.RowBudgetFirstColumnV1.target_source
#print axioms AEGIS.RowBudgetFirstColumnV1.row_order
#check @AEGIS.RowBudgetFirstColumnV1.row_order
#print axioms AEGIS.RowBudgetFirstColumnV1.first_column_contains
#check @AEGIS.RowBudgetFirstColumnV1.first_column_contains
#print axioms AEGIS.RowBudgetFirstColumnV1.all_rows_covered
#check @AEGIS.RowBudgetFirstColumnV1.all_rows_covered
#print axioms AEGIS.RowBudgetFirstColumnV1.first_column_mem
#check @AEGIS.RowBudgetFirstColumnV1.first_column_mem
