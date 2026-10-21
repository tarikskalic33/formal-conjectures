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
/- Entrywise transport from cached column checks to the original finite envelope. -/
import CvSCachedColumnV1
open scoped BigOperators
namespace AEGIS.CvSCachedEnvelopeJoinV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSIntervalMatrixProductV1
open AEGIS.CvSRowBudgetEnvelopeV1 AEGIS.CvSColumnEnvelopeV1 AEGIS.CvSListIntervalDotV1
open AEGIS.CvSCachedColumnV1

theorem envelope_entry_as_pair {ι κ ν : Type*} [Fintype κ] [Fintype ν] (p : ℕ)
    (Q : ι → ι → Iv) (X : κ → ι → Iv) (G : κ → κ → Iv)
    (T : κ → Iv) (Z : ν → ι → Iv) (LP2 : Iv) (i j : ι) :
    envelope p Q X G T Z LP2 i j = envelope p (fun (_ _ : Fin 2) => Q i j)
      (fun k (c : Fin 2) => if c.val = 0 then X k i else X k j) G T
      (fun r (c : Fin 2) => if c.val = 0 then Z r i else Z r j) LP2 0 1 := by
  simp only [envelope, sub, scale, add, matrixMul, congruence, weighted,
    dot, center, radius, Fin.val_zero, Fin.val_one, if_true,
    show ¬ (1 : ℕ) = 0 from by decide, if_false]

structure Column where
  x : Vector 141
  dx : Vector 141
  z : Vector 301
  gx : Vector 141
  gdx : Vector 141

def coeff {n : ℕ} (c : Fin n → Column) : Fin 141 → Fin n → Iv :=
  fun k i => (c i).x.values.getD k.val ⟨0, 0⟩
def residual {n : ℕ} (c : Fin n → Column) : Fin 301 → Fin n → Iv :=
  fun r i => (c i).z.values.getD r.val ⟨0, 0⟩

/-- Exact bridge for every pair, retaining all source and weighted-product identities. -/
theorem envelope_eq_cached {n : ℕ} (c : Fin n → Column)
    (Q : Fin n → Fin n → Iv) (G : List (List Iv)) (T : List Iv) (lp2 : Iv)
    (hG : G.length = 141) (hrows : ∀ k : Fin 141, (G.getD k.val []).length = 141)
    (hDX : ∀ i (k : Fin 141), (T.getD k.val ⟨0, 0⟩).mul 96
      ((c i).x.values.getD k.val ⟨0, 0⟩) = (c i).dx.values.getD k.val ⟨0, 0⟩)
    (hGX : ∀ j, (c j).gx.values = G.map (fun row => listDot 96 row (c j).x.values))
    (hGDX : ∀ j, (c j).gdx.values = G.map (fun row => listDot 96 row (c j).dx.values))
    (i j : Fin n) :
    envelope 96 Q (coeff c) (fun k l : Fin 141 => (G.getD k.val []).getD l.val ⟨0, 0⟩)
      (fun k : Fin 141 => T.getD k.val ⟨0, 0⟩) (residual c) lp2 i j =
    value (Q i j) lp2 (c i).x (c i).dx (c i).z (c j).z (c j).gx (c j).gdx := by
  rw [envelope_entry_as_pair]
  change envelope 96 (fun (_ _ : Fin 2) => Q i j)
    (twoColumns (c i).x.values (c j).x.values)
    (fun k l : Fin 141 => (G.getD k.val []).getD l.val ⟨0, 0⟩)
    (fun k : Fin 141 => T.getD k.val ⟨0, 0⟩)
    (twoColumns (c i).z.values (c j).z.values) lp2 0 1 = _
  rw [envelope_pair_eq 96 (Q i j) lp2 (c i).x.values (c j).x.values
    (c i).dx.values (c j).dx.values T (c i).z.values (c j).z.values G
    (c i).x.length_eq (c j).x.length_eq (c i).dx.length_eq (c j).dx.length_eq
    (c i).z.length_eq (c j).z.length_eq hG hrows (hDX i) (hDX j),
    ← hGX j, ← hGDX j, value_eq]

/-- Every checked entry produces the corresponding original real enclosure. -/
theorem stored_mem_of_cached {n : ℕ} (c : Fin n → Column)
    (Q : Fin n → Fin n → Iv) (G : List (List Iv)) (T : List Iv) (lp2 : Iv)
    (target : Fin n → Fin n → Iv)
    (hG : G.length = 141) (hrows : ∀ k : Fin 141, (G.getD k.val []).length = 141)
    (hDX : ∀ i (k : Fin 141), (T.getD k.val ⟨0, 0⟩).mul 96
      ((c i).x.values.getD k.val ⟨0, 0⟩) = (c i).dx.values.getD k.val ⟨0, 0⟩)
    (hGX : ∀ j, (c j).gx.values = G.map (fun row => listDot 96 row (c j).x.values))
    (hGDX : ∀ j, (c j).gdx.values = G.map (fun row => listDot 96 row (c j).dx.values))
    (hcheck : ∀ i j, contains (target i j) (downscale 16
      (value (Q i j) lp2 (c i).x (c i).dx (c i).z (c j).z (c j).gx (c j).gdx)) = true)
    (i j : Fin n) (v : ℝ)
    (hv : (envelope 96 Q (coeff c)
      (fun k l : Fin 141 => (G.getD k.val []).getD l.val ⟨0, 0⟩)
      (fun k : Fin 141 => T.getD k.val ⟨0, 0⟩) (residual c) lp2 i j).Mem 96 v) :
    (target i j).Mem 80 v := by
  apply mem_of_contains 80 (hcheck i j)
  have hh := downscale_mem 80 16 hv
  rw [envelope_eq_cached c Q G T lp2 hG hrows hDX hGX hGDX i j] at hh
  exact hh
end AEGIS.CvSCachedEnvelopeJoinV1
#print axioms AEGIS.CvSCachedEnvelopeJoinV1.envelope_entry_as_pair
#print axioms AEGIS.CvSCachedEnvelopeJoinV1.envelope_eq_cached
#print axioms AEGIS.CvSCachedEnvelopeJoinV1.stored_mem_of_cached
