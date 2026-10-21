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
/- Uniform interval enclosure for the actual algebraic row-budget expression. -/
import CvSIntervalMatrixProductV1

open scoped BigOperators
namespace AEGIS.CvSRowBudgetEnvelopeV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSIntervalMatrixProductV1

/-- Exact fixed-point encoding of an integer coefficient. -/
def point (p : ℕ) (z : ℤ) : Iv := ⟨z * 2 ^ p, z * 2 ^ p⟩

theorem point_mem (p : ℕ) (z : ℤ) : (point p z).Mem p (z : ℝ) := by
  simp [Iv.Mem, point, show (2 : ℝ) ^ p ≠ 0 by positivity]

/-- Interval coefficient multiplication, using the existing outward primitive. -/
def scale {ι κ : Type*} (p : ℕ) (s : Iv) (A : ι → κ → Iv) : ι → κ → Iv :=
  fun i j => s.mul p (A i j)

def add {ι κ : Type*} (A B : ι → κ → Iv) : ι → κ → Iv :=
  fun i j => (A i j).add (B i j)

def sub {ι κ : Type*} (A B : ι → κ → Iv) : ι → κ → Iv :=
  fun i j => (A i j).add (B i j).neg

/-- The tau-weighted coefficient enclosure used in the Gram tail. -/
def weighted {ι κ : Type*} (p : ℕ) (T : κ → Iv) (X : κ → ι → Iv) : κ → ι → Iv :=
  fun k i => (T k).mul p (X k i)

/-- 40*Q minus the finite residual Gram and the epsilon=1, T=13 Gram tail. -/
def envelope {ι κ ν : Type*} [Fintype κ] [Fintype ν] (p : ℕ)
    (Q : ι → ι → Iv) (X : κ → ι → Iv) (G : κ → κ → Iv)
    (T : κ → Iv) (Z : ν → ι → Iv) (LP2 : Iv) : ι → ι → Iv :=
  sub (sub (scale p (point p 40) Q) (matrixMul p (fun i r => Z r i) Z))
    (scale p LP2 (add
      (scale p (point p 2) (congruence p (weighted p T X) G))
      (scale p (point p 338) (congruence p X G))))

/-- The complete interval arithmetic layer of the proposed relative row certificate.
All input enclosures are explicit. No positivity, symmetry or RH assumption is used. -/
theorem envelope_mem {ι κ ν : Type*} [Fintype κ] [Fintype ν] (p : ℕ)
    (Q : ι → ι → Iv) (X : κ → ι → Iv) (G : κ → κ → Iv)
    (T : κ → Iv) (Z : ν → ι → Iv) (LP2 : Iv)
    (q : ι → ι → ℝ) (x : κ → ι → ℝ) (g : κ → κ → ℝ)
    (t : κ → ℝ) (z : ν → ι → ℝ) (lp2 : ℝ)
    (hQ : ∀ i j, (Q i j).Mem p (q i j))
    (hX : ∀ k i, (X k i).Mem p (x k i))
    (hG : ∀ k l, (G k l).Mem p (g k l))
    (hT : ∀ k, (T k).Mem p (t k))
    (hZ : ∀ r i, (Z r i).Mem p (z r i)) (hLP : LP2.Mem p lp2) :
    ∀ i j, (envelope p Q X G T Z LP2 i j).Mem p
      (40 * q i j - (∑ r, z r i * z r j) -
        lp2 * (2 * (∑ k, ∑ l, (t k * x k i) * (t l * x l j) * g k l) +
          338 * (∑ k, ∑ l, x k i * x l j * g k l))) := by
  intro i j
  have hDX : ∀ k i, (weighted p T X k i).Mem p (t k * x k i) :=
    fun k i => Iv.mem_mul p (hT k) (hX k i)
  have hDG := congruence_mem p (weighted p T X) G (fun k i => t k * x k i) g hDX hG i j
  have hGx := congruence_mem p X G x g hX hG i j
  have hZG := matrixMul_mem p (fun i r => Z r i) Z (fun i r => z r i) z
    (fun i r => hZ r i) hZ i j
  have htail := Iv.mem_mul p hLP
    (Iv.mem_add p (Iv.mem_mul p (point_mem p 2) hDG)
      (Iv.mem_mul p (point_mem p 338) hGx))
  have h := Iv.mem_add p
    (Iv.mem_add p (Iv.mem_mul p (point_mem p 40) (hQ i j)) (Iv.mem_neg p hZG))
    (Iv.mem_neg p htail)
  simpa only [envelope, sub, scale, add, Int.cast_ofNat, sub_eq_add_neg] using h

/-- The remaining output-table comparison is a finite executable condition.
This composes the full real envelope, symmetric hull and outward scale change. -/
theorem stored_envelope_mem_of_check {n : ℕ} {κ ν : Type*} [Fintype κ] [Fintype ν]
    (p d : ℕ) (target : Fin n → Fin n → Iv)
    (Q : Fin n → Fin n → Iv) (X : κ → Fin n → Iv) (G : κ → κ → Iv)
    (T : κ → Iv) (Z : ν → Fin n → Iv) (LP2 : Iv)
    (q : Fin n → Fin n → ℝ) (x : κ → Fin n → ℝ) (g : κ → κ → ℝ)
    (t : κ → ℝ) (z : ν → Fin n → ℝ) (lp2 : ℝ)
    (hQ : ∀ i j, (Q i j).Mem (p + d) (q i j))
    (hX : ∀ k i, (X k i).Mem (p + d) (x k i))
    (hG : ∀ k l, (G k l).Mem (p + d) (g k l))
    (hT : ∀ k, (T k).Mem (p + d) (t k))
    (hZ : ∀ r i, (Z r i).Mem (p + d) (z r i)) (hLP : LP2.Mem (p + d) lp2)
    (hc : tableCheck n target (fun i j => downscale d
      (hull (envelope (p + d) Q X G T Z LP2 i j)
        (envelope (p + d) Q X G T Z LP2 j i))) = true) :
    ∀ i j, (target i j).Mem p
      (40 * q i j - (∑ r, z r i * z r j) -
        lp2 * (2 * (∑ k, ∑ l, (t k * x k i) * (t l * x l j) * g k l) +
          338 * (∑ k, ∑ l, x k i * x l j * g k l))) := by
  apply tableCheck_sound p target _ _ hc
  intro i j
  exact downscale_mem p d (hull_mem_left (p + d)
    (envelope_mem (p + d) Q X G T Z LP2 q x g t z lp2 hQ hX hG hT hZ hLP i j))

end AEGIS.CvSRowBudgetEnvelopeV1
#print axioms AEGIS.CvSRowBudgetEnvelopeV1.point_mem
#print axioms AEGIS.CvSRowBudgetEnvelopeV1.envelope_mem

#print axioms AEGIS.CvSRowBudgetEnvelopeV1.stored_envelope_mem_of_check
