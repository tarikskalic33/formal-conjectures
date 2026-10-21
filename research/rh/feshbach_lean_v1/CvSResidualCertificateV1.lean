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

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Transfer of a finite rational certificate through entry enclosures

A symmetric nonnegative matrix of entry error bounds with row sums at most
`ε` loses at most `ε` in a quadratic lower bound. All entry enclosures and
the lower bound for the centre matrix remain explicit hypotheses. In
particular, this result supplies neither CvS entry enclosures nor H140 data.
-/

open scoped BigOperators ComplexConjugate

namespace AEGIS.CvSResidualCertificateV1

variable {ι : Type*} [Fintype ι]

/-- One cutoff controls an inverse-gap residual at every later truncation. -/
theorem exists_uniform_shifted_cutoff (C : ℝ) (hC : 0 ≤ C) (R : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ NP : ℕ, R < NP ∧ ∀ N : ℕ, NP ≤ N → C / ((N : ℝ) - R) < ε := by
  obtain ⟨NP, hNP⟩ := exists_nat_gt ((R : ℝ) + C / ε + 1)
  have hr : (R : ℝ) < NP := by
    have : 0 ≤ C / ε := div_nonneg hC hε.le
    linarith
  refine ⟨NP, by exact_mod_cast hr, ?_⟩
  intro N hN
  have hNN : (NP : ℝ) ≤ N := by exact_mod_cast hN
  have hden : 0 < (N : ℝ) - R := by linarith
  rw [div_lt_iff₀ hden]
  have hc : C / ε < (N : ℝ) - R := by linarith
  have := (div_lt_iff₀ hε).mp hc
  nlinarith

/-- The scalar estimate used for each entry of a symmetric residual. -/
theorem residual_entry_le (x y e r : ℝ) (he : |e| ≤ r) :
    x * y * e ≤ r * (x ^ 2 + y ^ 2) / 2 := by
  have hxy : |x * y| ≤ (x ^ 2 + y ^ 2) / 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
  calc
    x * y * e ≤ |x * y * e| := le_abs_self _
    _ = |x * y| * |e| := abs_mul _ _
    _ ≤ ((x ^ 2 + y ^ 2) / 2) * r :=
      mul_le_mul hxy he (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- Entry intervals give an outward error radius about any chosen centre. -/
theorem abs_sub_le_of_enclosure (a c lo hi : ℝ) (hlo : lo ≤ a) (hhi : a ≤ hi) :
    |a - c| ≤ max (c - lo) (hi - c) := by
  rw [abs_le]
  have hl := le_max_left (c - lo) (hi - c)
  have hh := le_max_right (c - lo) (hi - c)
  constructor <;> linarith

/-- A symmetric entry majorant controls the entire real quadratic form. -/
theorem residual_quadratic_le (E R : ι → ι → ℝ) (ε : ℝ)
    (hE : ∀ i j, |E i j| ≤ R i j)
    (hsym : ∀ i j, R i j = R j i)
    (hrow : ∀ i, ∑ j, R i j ≤ ε) (x : ι → ℝ) :
    (∑ i, ∑ j, x i * x j * E i j) ≤ ε * ∑ i, x i ^ 2 := by
  have hcollapse : (∑ i, ∑ j, R i j * (x i ^ 2 + x j ^ 2) / 2) =
      ∑ i, (x i ^ 2) * ∑ j, R i j := by
    have hswap : (∑ i, ∑ j, R i j * x j ^ 2 / 2) =
        ∑ i, ∑ j, R i j * x i ^ 2 / 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hsym j i]
    simp_rw [mul_add, add_div, Finset.sum_add_distrib]
    rw [hswap]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    ring
  calc
    (∑ i, ∑ j, x i * x j * E i j) ≤
        ∑ i, ∑ j, R i j * (x i ^ 2 + x j ^ 2) / 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        residual_entry_le _ _ _ _ (hE i j)
    _ = ∑ i, (x i ^ 2) * ∑ j, R i j := hcollapse
    _ ≤ ∑ i, (x i ^ 2) * ε :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _)
    _ = ε * ∑ i, x i ^ 2 := by rw [Finset.mul_sum]; congr 1; funext i; ring

/-- An `ε`-coercive centre and a residual row budget `ε` certify the actual matrix. -/
theorem actual_quadratic_nonneg (A A₀ R : ι → ι → ℝ) (ε : ℝ)
    (hencl : ∀ i j, |A i j - A₀ i j| ≤ R i j)
    (hsym : ∀ i j, R i j = R j i)
    (hrow : ∀ i, ∑ j, R i j ≤ ε)
    (hcentre : ∀ x : ι → ℝ, ε * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, x i * x j * A₀ i j)
    (x : ι → ℝ) : 0 ≤ ∑ i, ∑ j, x i * x j * A i j := by
  have herr := residual_quadratic_le (fun i j => A₀ i j - A i j) R ε
    (fun i j => by rw [abs_sub_comm]; exact hencl i j) hsym hrow x
  simp_rw [mul_sub, Finset.sum_sub_distrib] at herr
  have hc := hcentre x
  linarith

/-- Real matrix positivity applies to complex vectors by splitting their coordinates. -/
theorem actual_hermitian_nonneg (A A₀ R : ι → ι → ℝ) (ε : ℝ)
    (hencl : ∀ i j, |A i j - A₀ i j| ≤ R i j)
    (hsym : ∀ i j, R i j = R j i)
    (hrow : ∀ i, ∑ j, R i j ≤ ε)
    (hcentre : ∀ x : ι → ℝ, ε * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, x i * x j * A₀ i j)
    (z : ι → ℂ) : 0 ≤ (∑ i, ∑ j, conj (z i) * z j * (A i j : ℂ)).re := by
  have hx := actual_quadratic_nonneg A A₀ R ε hencl hsym hrow hcentre (fun i => (z i).re)
  have hy := actual_quadratic_nonneg A A₀ R ε hencl hsym hrow hcentre (fun i => (z i).im)
  have hexp : (∑ i, ∑ j, conj (z i) * z j * (A i j : ℂ)).re =
      (∑ i, ∑ j, (z i).re * (z j).re * A i j) +
        ∑ i, ∑ j, (z i).im * (z j).im * A i j := by
    change Complex.reAddGroupHom _ = _
    simp only [map_sum]
    change (∑ i, ∑ j, (conj (z i) * z j * (A i j : ℂ)).re) = _
    simp only [Complex.mul_re, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      neg_mul, sub_neg_eq_add, add_mul, Finset.sum_add_distrib]
  rw [hexp]
  exact add_nonneg hx hy

end AEGIS.CvSResidualCertificateV1

#check @AEGIS.CvSResidualCertificateV1.exists_uniform_shifted_cutoff
#print axioms AEGIS.CvSResidualCertificateV1.exists_uniform_shifted_cutoff
#check @AEGIS.CvSResidualCertificateV1.residual_entry_le
#check @AEGIS.CvSResidualCertificateV1.abs_sub_le_of_enclosure
#check @AEGIS.CvSResidualCertificateV1.residual_quadratic_le
#check @AEGIS.CvSResidualCertificateV1.actual_quadratic_nonneg
#check @AEGIS.CvSResidualCertificateV1.actual_hermitian_nonneg
#print axioms AEGIS.CvSResidualCertificateV1.residual_entry_le
#print axioms AEGIS.CvSResidualCertificateV1.abs_sub_le_of_enclosure
#print axioms AEGIS.CvSResidualCertificateV1.residual_quadratic_le
#print axioms AEGIS.CvSResidualCertificateV1.actual_quadratic_nonneg
#print axioms AEGIS.CvSResidualCertificateV1.actual_hermitian_nonneg
