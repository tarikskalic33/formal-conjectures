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
/- Exact complex quadratic-form interpretation of the certified real Gram tail. -/
import CvSRealTailMatrixV1
import CvSFiniteCongruenceV1
open scoped BigOperators ComplexConjugate
namespace AEGIS.CvSRealTailFormV1
open AEGIS.CvSRealTailMatrixV1 AEGIS.CvSFiniteCongruenceV1

/-- Scalar weighting commutes with the finite coefficient map. -/
theorem weighted_apply {ι κ : Type*} [Fintype ι]
    (x : κ → ι → ℝ) (t : κ → ℝ) (v : ι → ℂ) (k : κ) :
    (∑ i, ((t k * x k i : ℝ) : ℂ) * v i) =
      (∑ i, (x k i : ℂ) * v i) * (t k : ℂ) := by
  simp only [Complex.ofReal_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The certified tail matrix represents the epsilon=1, T=13 majorant exactly.
No symmetry or positivity is required for this finite identity. -/
theorem tail_form_eq (x : Fin 141 → Fin 139 → ℝ)
    (g : Fin 141 → Fin 141 → ℝ) (t : Fin 141 → ℝ) (lp2 : ℝ)
    (v : Fin 139 → ℂ) :
    (∑ i, ∑ j, v i * conj (v j) * (tailMatrix x g t lp2 i j : ℂ)).re =
      lp2 * (2 * (∑ k, ∑ l,
        ((∑ i, (x k i : ℂ) * v i) * (t k : ℂ)) *
        conj ((∑ j, (x l j : ℂ) * v j) * (t l : ℂ)) * (g k l : ℂ)).re +
      338 * (∑ k, ∑ l, (∑ i, (x k i : ℂ) * v i) *
        conj (∑ j, (x l j : ℂ) * v j) * (g k l : ℂ)).re) := by
  have he : (∑ i, ∑ j, v i * conj (v j) * (tailMatrix x g t lp2 i j : ℂ)) =
      (lp2 : ℂ) * (2 * (∑ i, ∑ j, v i * conj (v j) *
        (realCongruence (fun k i => t k * x k i) g i j : ℂ)) +
      338 * (∑ i, ∑ j, v i * conj (v j) * (realCongruence x g i j : ℂ))) := by
    calc
      _ = ∑ i, ∑ j, (((lp2 : ℂ) * 2) * (v i * conj (v j) *
          (realCongruence (fun k i => t k * x k i) g i j : ℂ)) +
          ((lp2 : ℂ) * 338) * (v i * conj (v j) * (realCongruence x g i j : ℂ))) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [tailMatrix, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_ofNat]
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
  rw [he]
  simp only [realCongruence, quadratic_form_real_congruence, weighted_apply,
    Complex.re_ofReal_mul, Complex.add_re]
  simp [Complex.mul_re]

/-- Applying a real finite residual matrix preserves the original coefficient action. -/
theorem residual_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (y : ι → ℝ) (x : κ → ℝ) (lam : κ → ι → ℝ) (v : ι → ℂ) :
    (∑ i, ((y i - ∑ j, x j * lam j i : ℝ) : ℂ) * v i) =
      (∑ i, (y i : ℂ) * v i) -
        ∑ j, (x j : ℂ) * (∑ i, (lam j i : ℂ) * v i) := by
  simp only [Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_mul,
    sub_mul, Finset.sum_sub_distrib]
  congr 1
  exact transformed_coeff_linear (fun (_ : Unit) j => (x j : ℂ))
    (fun j i => (lam j i : ℂ)) v ()

/-- Exact reindexing of all finite residual rows, including both endpoints. -/
theorem sum_centered_rows {V : Type*} [AddCommMonoid V] (N : ℕ) (f : ℤ → V) :
    (∑ r : Fin (2 * N + 1), f ((r.val : ℤ) - N)) =
      ∑ m ∈ Finset.Icc (-(N : ℤ)) N, f m := by
  apply Finset.sum_bij (fun r _ => (r.val : ℤ) - N)
  · intro r _
    simp only [Finset.mem_Icc]
    have hr := r.isLt
    constructor <;> omega
  · intro r _ s _ h
    apply Fin.ext
    omega
  · intro m hm
    simp only [Finset.mem_Icc] at hm
    refine ⟨⟨(m + N).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    change ((m + (N : ℤ)).toNat : ℤ) - N = m
    omega
  · intro r _
    rfl

end AEGIS.CvSRealTailFormV1
#print axioms AEGIS.CvSRealTailFormV1.weighted_apply
#print axioms AEGIS.CvSRealTailFormV1.tail_form_eq
#print axioms AEGIS.CvSRealTailFormV1.residual_apply

#print axioms AEGIS.CvSRealTailFormV1.sum_centered_rows
