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
/- Exact point membership for the unchanged rational projection witness. -/
import CvSCachedSourceProductV1
namespace AEGIS.CvSCachedPointV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSCachedColumnV1

theorem point_entry {n : ℕ} (a : Vector n)
    (hc : a.values.all (fun I => decide (I.lo = I.hi)) = true) (k : Fin n) :
    (a.values.getD k.val ⟨0, 0⟩).lo = (a.values.getD k.val ⟨0, 0⟩).hi := by
  have hk : k.val < a.values.length := by rw [a.length_eq]; exact k.isLt
  have hm : a.values.getD k.val ⟨0, 0⟩ ∈ a.values := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    exact List.getElem_mem hk
  exact of_decide_eq_true (List.all_eq_true.mp hc _ hm)

theorem point_mem (p : ℕ) (I : Iv) (hI : I.lo = I.hi) :
    I.Mem p ((I.lo : ℝ) / 2^p) := by
  constructor
  · exact le_rfl
  · exact div_le_div_of_nonneg_right (le_of_eq (congrArg (fun z : ℤ => (z : ℝ)) hI))
      (by positivity)
end AEGIS.CvSCachedPointV1
#print axioms AEGIS.CvSCachedPointV1.point_entry
#print axioms AEGIS.CvSCachedPointV1.point_mem
