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
/- Exact two-column execution of the existing complete interval envelope. -/
import CvSListIntervalMixedV1
import CvSRowBudgetEnvelopeV1
namespace AEGIS.CvSColumnEnvelopeV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSIntervalMatrixProductV1
open AEGIS.CvSRowBudgetEnvelopeV1 AEGIS.CvSListIntervalDotV1 AEGIS.CvSListIntervalMixedV1

def twoColumns {n : ℕ} (a b : List Iv) : Fin n → Fin 2 → Iv :=
  fun k j => if j.val = 0 then a.getD k.val ⟨0, 0⟩ else b.getD k.val ⟨0, 0⟩

def columnValue (p : ℕ) (q : Iv) (a da u v gy gdy : List Iv) (lp2 : Iv) : Iv :=
  (((point p 40).mul p q).add (listDot p u v).neg).add
    (lp2.mul p (((point p 2).mul p (listDot p da gdy)).add
      ((point p 338).mul p (listDot p a gy)))).neg

/-- Each mixed entry uses one cached right Gram column, at every finite size. -/
theorem envelope_pair_eq (p : ℕ) {n r : ℕ} (q lp2 : Iv)
    (a b da db T u v : List Iv) (G : List (List Iv))
    (ha : a.length = n) (hb : b.length = n) (hda : da.length = n) (hdb : db.length = n)
    (hu : u.length = r) (hv : v.length = r) (hG : G.length = n)
    (hrows : ∀ k : Fin n, (G.getD k.val []).length = n)
    (hDa : ∀ k : Fin n, (T.getD k.val ⟨0, 0⟩).mul p (a.getD k.val ⟨0, 0⟩) = da.getD k.val ⟨0, 0⟩)
    (hDb : ∀ k : Fin n, (T.getD k.val ⟨0, 0⟩).mul p (b.getD k.val ⟨0, 0⟩) = db.getD k.val ⟨0, 0⟩) :
    envelope p (fun (_ _ : Fin 2) => q) (twoColumns (n := n) a b)
      (fun k l : Fin n => (G.getD k.val []).getD l.val ⟨0, 0⟩)
      (fun k : Fin n => T.getD k.val ⟨0, 0⟩) (twoColumns (n := r) u v) lp2 0 1 =
      columnValue p q a da u v (G.map (fun row => listDot p row b))
        (G.map (fun row => listDot p row db)) lp2 := by
  have hw : weighted p (fun k : Fin n => T.getD k.val ⟨0, 0⟩) (twoColumns a b) =
      twoColumns da db := by
    funext k j
    by_cases h : j.val = 0
    · simpa only [weighted, twoColumns, if_pos h] using hDa k
    · simpa only [weighted, twoColumns, if_neg h] using hDb k
  have hd : congruence p (twoColumns (n := n) da db)
      (fun k l : Fin n => (G.getD k.val []).getD l.val ⟨0, 0⟩) (0 : Fin 2) 1 =
      listDot p da (G.map (fun row => listDot p row db)) :=
    mixed_listCongruence_eq p da db G hda hdb hG hrows
  have hg : congruence p (twoColumns (n := n) a b)
      (fun k l : Fin n => (G.getD k.val []).getD l.val ⟨0, 0⟩) (0 : Fin 2) 1 =
      listDot p a (G.map (fun row => listDot p row b)) :=
    mixed_listCongruence_eq p a b G ha hb hG hrows
  have hz : matrixMul p (fun (i : Fin 2) (k : Fin r) => twoColumns u v k i)
      (twoColumns u v) (0 : Fin 2) 1 = listDot p u v :=
    (listDot_eq_dot p u v hu hv).symm
  simp only [envelope, sub, scale, add]
  rw [hw, hd, hg, hz]
  rfl

end AEGIS.CvSColumnEnvelopeV1
#print axioms AEGIS.CvSColumnEnvelopeV1.envelope_pair_eq
