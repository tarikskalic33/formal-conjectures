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
/- Exact list execution for off-diagonal/mixed interval congruence entries. -/
import CvSListIntervalDotV1
namespace AEGIS.CvSListIntervalMixedV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSIntervalMatrixProductV1 AEGIS.CvSListIntervalDotV1

/-- Two distinct columns are allowed; neither symmetry nor positivity is assumed. -/
theorem mixed_listCongruence_eq (p : ℕ) {n : ℕ} (X Y : List Iv) (G : List (List Iv))
    (hX : X.length = n) (hY : Y.length = n) (hG : G.length = n)
    (hrows : ∀ k : Fin n, (G.getD k.val []).length = n) :
    matrixMul p (fun (_ : Fin 1) (k : Fin n) => X.getD k.val ⟨0, 0⟩)
      (matrixMul p (fun k l : Fin n => (G.getD k.val []).getD l.val ⟨0, 0⟩)
        (fun (k : Fin n) (_ : Fin 1) => Y.getD k.val ⟨0, 0⟩)) 0 0 =
      listDot p X (G.map (fun row => listDot p row Y)) := by
  rw [listDot_eq_dot p X _ hX (by simpa using hG)]
  change dot p (fun k : Fin n => X.getD k.val ⟨0, 0⟩)
    (fun k : Fin n => dot p (fun l : Fin n => (G.getD k.val []).getD l.val ⟨0, 0⟩)
      (fun l : Fin n => Y.getD l.val ⟨0, 0⟩)) = _
  congr 1
  funext k
  rw [getD_map_lt G (fun row => listDot p row Y) ⟨0, 0⟩ [] (by omega)]
  exact (listDot_eq_dot p (G.getD k.val []) Y (hrows k) hY).symm

end AEGIS.CvSListIntervalMixedV1
#print axioms AEGIS.CvSListIntervalMixedV1.mixed_listCongruence_eq
#check @AEGIS.CvSListIntervalMixedV1.mixed_listCongruence_eq
