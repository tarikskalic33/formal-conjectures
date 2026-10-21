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
/- Cached interval vectors and exact evaluation of the unchanged row envelope. -/
import CvSPackedIntervalDotV1
import CvSColumnEnvelopeV1
namespace AEGIS.CvSCachedColumnV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSIntervalMatrixProductV1
open AEGIS.CvSListIntervalDotV1 AEGIS.CvSColumnEnvelopeV1
open AEGIS.CvSPackedIntervalDotV1

/-- A numerical cache carries its source identity and every packing hypothesis. -/
structure Vector (n : ℕ) where
  values : List Iv
  cache : PackedIntervalRow
  length_eq : values.length = n
  components : bounded (2^128) values
  preparation : cache = prepareInterval (2^280) (2^128) values

def evalDot {n : ℕ} (a b : Vector n) : Iv :=
  cachedIntervalDot 96 (2^280) (2^128) a.cache b.cache

theorem evalDot_eq {n : ℕ} (hn : 0 < n) (hn' : n ≤ 301) (a b : Vector n) :
    evalDot a b = listDot 96 a.values b.values := by
  apply cachedIntervalDot_eq 96 (2^280) (2^128) a.values b.values a.cache b.cache
    a.preparation b.preparation
  · rw [a.length_eq]; exact hn
  · rw [a.length_eq, b.length_eq]
  · exact a.components
  · exact b.components
  · rw [a.length_eq]
    have h : 301 * 301 * (2 * 2^128 * (2 * 2^128)) < (2^280 : ℕ) := by decide +kernel
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_self_le_mul_self hn')) h

def value (q lp2 : Iv) (a da : Vector 141) (u v : Vector 301)
    (gy gdy : Vector 141) : Iv :=
  (((AEGIS.CvSRowBudgetEnvelopeV1.point 96 40).mul 96 q).add (evalDot u v).neg).add
    (lp2.mul 96 (((AEGIS.CvSRowBudgetEnvelopeV1.point 96 2).mul 96 (evalDot da gdy)).add
      ((AEGIS.CvSRowBudgetEnvelopeV1.point 96 338).mul 96 (evalDot a gy)))).neg

theorem value_eq (q lp2 : Iv) (a da : Vector 141) (u v : Vector 301)
    (gy gdy : Vector 141) :
    value q lp2 a da u v gy gdy =
      columnValue 96 q a.values da.values u.values v.values gy.values gdy.values lp2 := by
  simp only [value, evalDot_eq (by decide : 0 < 301) (by decide : 301 ≤ 301),
    evalDot_eq (by decide : 0 < 141) (by decide : 141 ≤ 301), columnValue]

/-- A cached Gram-column product is exactly the original row-by-column product. -/
theorem gram_product_eq (rows : List (Vector 141)) (a : Vector 141) :
    rows.map (fun g => evalDot g a) =
      (rows.map Vector.values).map (fun g => listDot 96 g a.values) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro g _
  exact evalDot_eq (by decide) (by decide) g a

end AEGIS.CvSCachedColumnV1
#print axioms AEGIS.CvSCachedColumnV1.evalDot_eq
#print axioms AEGIS.CvSCachedColumnV1.value_eq
#print axioms AEGIS.CvSCachedColumnV1.gram_product_eq
