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
/- Soundness of the exact midpoint-radius matrix product used by the row certificate. -/
import Mathlib.Algebra.BigOperators.Field
import RHFixIntervalV1
import CvSMidpointRadiusV1

open scoped BigOperators
namespace AEGIS.CvSIntervalMatrixProductV1
open AEGIS.RHFixIntervalV1

/-- Integer midpoint with floor rounding, including negative endpoints. -/
def mid (I : Iv) : ℤ := (I.lo + I.hi) / 2

/-- Radius covers both sides even when floor rounding is asymmetric. -/
def rad (I : Iv) : ℤ := max (mid I - I.lo) (I.hi - mid I)

/-- The original interval contract gives the exact midpoint-radius error. -/
theorem midpoint_error (p : ℕ) {I : Iv} {x : ℝ} (hx : I.Mem p x) :
    |x - (mid I : ℝ) / 2 ^ p| ≤ (rad I : ℝ) / 2 ^ p := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hl : (mid I : ℝ) - I.lo ≤ (rad I : ℝ) := by
    exact_mod_cast (le_max_left (mid I - I.lo) (I.hi - mid I))
  have hh : (I.hi : ℝ) - mid I ≤ (rad I : ℝ) := by
    exact_mod_cast (le_max_right (mid I - I.lo) (I.hi - mid I))
  have hld := div_le_div_of_nonneg_right hl hp.le
  have hhd := div_le_div_of_nonneg_right hh hp.le
  simp only [sub_div] at hld hhd
  obtain ⟨hx1, hx2⟩ := hx
  rw [abs_le]
  constructor <;> linarith

/-- Product center numerator at the squared fixed-point scale. -/
def center {ι : Type*} [Fintype ι] (A B : ι → Iv) : ℤ :=
  ∑ k, mid (A k) * mid (B k)

/-- Exact product-radius numerator, before outward rescaling. -/
def radius {ι : Type*} [Fintype ι] (A B : ι → Iv) : ℤ :=
  ∑ k, (|mid (A k)| * rad (B k) + rad (A k) * |mid (B k)| + rad (A k) * rad (B k))

/-- The same outward Qp product as the certificate generator. -/
def dot {ι : Type*} [Fintype ι] (p : ℕ) (A B : ι → Iv) : Iv :=
  ⟨fdiv p (center A B - radius A B), cdiv p (center A B + radius A B)⟩

/-- Uniform soundness for every finite real matrix-product entry. -/
theorem dot_mem {ι : Type*} [Fintype ι] (p : ℕ) (A B : ι → Iv) (a b : ι → ℝ)
    (ha : ∀ k, (A k).Mem p (a k)) (hb : ∀ k, (B k).Mem p (b k)) :
    (dot p A B).Mem p (∑ k, a k * b k) := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have h := AEGIS.CvSMidpointRadiusV1.sum_product_error a b
    (fun k => (mid (A k) : ℝ) / 2 ^ p) (fun k => (mid (B k) : ℝ) / 2 ^ p)
    (fun k => (rad (A k) : ℝ) / 2 ^ p) (fun k => (rad (B k) : ℝ) / 2 ^ p)
    (fun k => midpoint_error p (ha k)) (fun k => midpoint_error p (hb k))
  have hc : (∑ k, (mid (A k) : ℝ) / 2 ^ p * ((mid (B k) : ℝ) / 2 ^ p)) =
      (center A B : ℝ) / (2 ^ p * 2 ^ p) := by
    simp only [center, Int.cast_sum, Int.cast_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    exact div_mul_div_comm _ _ _ _
  have hr : (∑ k, (|(mid (A k) : ℝ) / 2 ^ p| * ((rad (B k) : ℝ) / 2 ^ p) +
      (rad (A k) : ℝ) / 2 ^ p * |(mid (B k) : ℝ) / 2 ^ p| +
      (rad (A k) : ℝ) / 2 ^ p * ((rad (B k) : ℝ) / 2 ^ p))) =
      (radius A B : ℝ) / (2 ^ p * 2 ^ p) := by
    simp only [radius, Int.cast_sum, Int.cast_add, Int.cast_mul, Int.cast_abs,
      abs_div, abs_of_pos hp, div_mul_div_comm, ← add_div, ← Finset.sum_div]
  rw [hc, hr, abs_le] at h
  have hlo : ((center A B - radius A B : ℤ) : ℝ) / 2 ^ p / 2 ^ p ≤
      ∑ k, a k * b k := by
    push_cast
    rw [div_div, sub_div]
    linarith [h.1]
  have hhi : (∑ k, a k * b k) ≤
      ((center A B + radius A B : ℤ) : ℝ) / 2 ^ p / 2 ^ p := by
    push_cast
    rw [div_div, add_div]
    linarith [h.2]
  constructor
  · exact (div_le_div_of_nonneg_right (fdiv_le p _) hp.le).trans hlo
  · exact hhi.trans (div_le_div_of_nonneg_right (le_cdiv p _) hp.le)

/-- Matrix multiplication follows the entrywise interval contract. -/
def matrixMul {ι κ ν : Type*} [Fintype κ] (p : ℕ)
    (A : ι → κ → Iv) (B : κ → ν → Iv) : ι → ν → Iv :=
  fun i j => dot p (A i) (fun k => B k j)

theorem matrixMul_mem {ι κ ν : Type*} [Fintype κ] (p : ℕ)
    (A : ι → κ → Iv) (B : κ → ν → Iv) (a : ι → κ → ℝ) (b : κ → ν → ℝ)
    (ha : ∀ i k, (A i k).Mem p (a i k)) (hb : ∀ k j, (B k j).Mem p (b k j)) :
    ∀ i j, (matrixMul p A B i j).Mem p (∑ k, a i k * b k j) :=
  fun i j => dot_mem p (A i) (fun k => B k j) (a i) (fun k => b k j)
    (ha i) (fun k => hb k j)

/-- The generator forms a congruence in this order: X^T * (G * X). -/
def congruence {ι κ : Type*} [Fintype κ] (p : ℕ)
    (X : κ → ι → Iv) (G : κ → κ → Iv) : ι → ι → Iv :=
  matrixMul p (fun i k => X k i) (matrixMul p G X)

/-- Uniform soundness of Gram and weighted-tail congruences. -/
theorem congruence_mem {ι κ : Type*} [Fintype κ] (p : ℕ)
    (X : κ → ι → Iv) (G : κ → κ → Iv) (x : κ → ι → ℝ) (g : κ → κ → ℝ)
    (hx : ∀ k i, (X k i).Mem p (x k i)) (hg : ∀ k l, (G k l).Mem p (g k l)) :
    ∀ i j, (congruence p X G i j).Mem p
      (∑ k, ∑ l, x k i * x l j * g k l) := by
  intro i j
  have h := matrixMul_mem p (fun i k => X k i) (matrixMul p G X)
    (fun i k => x k i) (fun k j => ∑ l, g k l * x l j)
    (fun i k => hx k i) (matrixMul_mem p G X g x hg hx) i j
  have he : (∑ k, x k i * ∑ l, g k l * x l j) =
      ∑ k, ∑ l, x k i * x l j * g k l := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simpa only [congruence, he] using h

/-- The symmetric hull only enlarges intervals. -/
def hull (I J : Iv) : Iv := ⟨min I.lo J.lo, max I.hi J.hi⟩

theorem hull_mem_left (p : ℕ) {I J : Iv} {x : ℝ} (h : I.Mem p x) :
    (hull I J).Mem p x := by
  have hp : (0 : ℝ) ≤ 2 ^ p := by positivity
  exact ⟨(div_le_div_of_nonneg_right (by exact_mod_cast min_le_left I.lo J.lo) hp).trans h.1,
    h.2.trans (div_le_div_of_nonneg_right (by exact_mod_cast le_max_left I.hi J.hi) hp)⟩

/-- Drop d fractional bits using outward integer division. -/
def downscale (d : ℕ) (I : Iv) : Iv := ⟨fdiv d I.lo, cdiv d I.hi⟩

theorem downscale_mem (p d : ℕ) {I : Iv} {x : ℝ} (h : I.Mem (p + d) x) :
    (downscale d I).Mem p x := by
  have hp : (0 : ℝ) ≤ 2 ^ p := by positivity
  have he : (2 : ℝ) ^ (p + d) = 2 ^ d * 2 ^ p := by rw [pow_add, mul_comm]
  have hlo := div_le_div_of_nonneg_right (fdiv_le d I.lo) hp
  have hhi := div_le_div_of_nonneg_right (le_cdiv d I.hi) hp
  rw [div_div, ← he] at hlo hhi
  exact ⟨hlo.trans h.1, h.2.trans hhi⟩

/-- Exact embedding into a scale with d additional fractional bits. -/
def upscale (d : ℕ) (I : Iv) : Iv := ⟨I.lo * 2 ^ d, I.hi * 2 ^ d⟩

theorem upscale_mem (p d : ℕ) {I : Iv} {x : ℝ} (h : I.Mem p x) :
    (upscale d I).Mem (p + d) x := by
  have he : ∀ z : ℤ, ((z * 2 ^ d : ℤ) : ℝ) / 2 ^ (p + d) = (z : ℝ) / 2 ^ p := by
    intro z
    push_cast
    rw [pow_add]
    field_simp
  simpa only [Iv.Mem, upscale, he] using h

/-- Executable containment in a stored certificate interval. -/
def contains (target evaluated : Iv) : Bool :=
  decide (target.lo ≤ evaluated.lo) && decide (evaluated.hi ≤ target.hi)

theorem mem_of_contains (p : ℕ) {target evaluated : Iv} {x : ℝ}
    (hc : contains target evaluated = true) (hx : evaluated.Mem p x) :
    target.Mem p x := by
  simp only [contains, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hp : (0 : ℝ) ≤ 2 ^ p := by positivity
  exact ⟨(div_le_div_of_nonneg_right (by exact_mod_cast hc.1) hp).trans hx.1,
    hx.2.trans (div_le_div_of_nonneg_right (by exact_mod_cast hc.2) hp)⟩

/-- Pure finite output-table comparison; contains no analytic assumption. -/
def tableCheck (n : ℕ) (target evaluated : Fin n → Fin n → Iv) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun j => contains (target i j) (evaluated i j)

theorem tableCheck_sound {n : ℕ} (p : ℕ) (target evaluated : Fin n → Fin n → Iv)
    (a : Fin n → Fin n → ℝ) (hc : tableCheck n target evaluated = true)
    (ha : ∀ i j, (evaluated i j).Mem p (a i j)) :
    ∀ i j, (target i j).Mem p (a i j) := by
  simp only [tableCheck, List.all_eq_true, List.mem_finRange, forall_const] at hc
  intro i j
  exact mem_of_contains p (hc i j) (ha i j)

end AEGIS.CvSIntervalMatrixProductV1
#print axioms AEGIS.CvSIntervalMatrixProductV1.midpoint_error
#print axioms AEGIS.CvSIntervalMatrixProductV1.dot_mem

#print axioms AEGIS.CvSIntervalMatrixProductV1.matrixMul_mem
#print axioms AEGIS.CvSIntervalMatrixProductV1.congruence_mem
#print axioms AEGIS.CvSIntervalMatrixProductV1.hull_mem_left
#print axioms AEGIS.CvSIntervalMatrixProductV1.downscale_mem

#print axioms AEGIS.CvSIntervalMatrixProductV1.upscale_mem
#print axioms AEGIS.CvSIntervalMatrixProductV1.mem_of_contains
#print axioms AEGIS.CvSIntervalMatrixProductV1.tableCheck_sound
