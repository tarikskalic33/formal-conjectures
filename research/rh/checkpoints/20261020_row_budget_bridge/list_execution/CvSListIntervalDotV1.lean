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
/- List execution of the already proved midpoint-radius dot product.
The algebra and all rounding endpoints are unchanged. -/
import CvSIntervalMatrixProductV1
import Mathlib.Algebra.BigOperators.Fin
open scoped BigOperators
namespace AEGIS.CvSListIntervalDotV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSIntervalMatrixProductV1

def listDot (p : ℕ) (A B : List Iv) : Iv :=
  let c := (List.zipWith (fun a b => mid a * mid b) A B).sum
  let r := (List.zipWith (fun a b => |mid a| * rad b + rad a * |mid b| + rad a * rad b) A B).sum
  ⟨fdiv p (c - r), cdiv p (c + r)⟩

theorem zipWith_ofFn {α β γ : Type*} {n : ℕ} (f : α → β → γ)
    (a : Fin n → α) (b : Fin n → β) :
    List.zipWith f (List.ofFn a) (List.ofFn b) = List.ofFn (fun i => f (a i) (b i)) := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp at hj
  simp

/-- Uniform equality to the existing checker dot; no estimate is weakened. -/
theorem listDot_ofFn (p : ℕ) {n : ℕ} (a b : Fin n → Iv) :
    listDot p (List.ofFn a) (List.ofFn b) = dot p a b := by
  simp only [listDot, zipWith_ofFn, List.sum_ofFn, dot, center, radius]

theorem ofFn_getD {α : Type*} (A : List α) (d : α) {n : ℕ} (ha : A.length = n) :
    List.ofFn (fun k : Fin n => A.getD k.val d) = A := by
  apply List.ext_getElem (by simp [ha])
  intro i hi hj
  simp only [List.getElem_ofFn, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj, Option.getD_some]

/-- Literals can be evaluated in one pass instead of repeatedly indexed finite sums. -/
theorem listDot_eq_dot (p : ℕ) {n : ℕ} (A B : List Iv)
    (ha : A.length = n) (hb : B.length = n) :
    listDot p A B = dot p (fun k : Fin n => A.getD k.val ⟨0, 0⟩)
      (fun k : Fin n => B.getD k.val ⟨0, 0⟩) := by
  rw [← listDot_ofFn, ofFn_getD A ⟨0, 0⟩ ha, ofFn_getD B ⟨0, 0⟩ hb]

theorem getD_map_lt {α β : Type*} (A : List α) (f : α → β) (d : β) (e : α)
    {k : ℕ} (hk : k < A.length) : (A.map f).getD k d = f (A.getD k e) := by
  simp [List.getD_eq_getElem?_getD, hk]

/-- A complete congruence entry can use materialized inner dot products. -/
theorem listCongruence_eq (p : ℕ) {n : ℕ} (X : List Iv) (G : List (List Iv))
    (hX : X.length = n) (hG : G.length = n)
    (hrows : ∀ k : Fin n, (G.getD k.val []).length = n) :
    congruence p (fun (k : Fin n) (_ : Fin 1) => X.getD k.val ⟨0, 0⟩)
      (fun k l : Fin n => (G.getD k.val []).getD l.val ⟨0, 0⟩) 0 0 =
      listDot p X (G.map (fun row => listDot p row X)) := by
  rw [listDot_eq_dot p X _ hX (by simpa using hG)]
  change dot p (fun k : Fin n => X.getD k.val ⟨0, 0⟩)
    (fun k : Fin n => dot p (fun l : Fin n => (G.getD k.val []).getD l.val ⟨0, 0⟩)
      (fun l : Fin n => X.getD l.val ⟨0, 0⟩)) = _
  congr 1
  funext k
  rw [getD_map_lt G (fun row => listDot p row X) ⟨0, 0⟩ [] (by omega)]
  exact (listDot_eq_dot p (G.getD k.val []) X (hrows k) hX).symm

end AEGIS.CvSListIntervalDotV1
#print axioms AEGIS.CvSListIntervalDotV1.listDot_eq_dot
#print axioms AEGIS.CvSListIntervalDotV1.listCongruence_eq
