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

import RHCheckSoundV1

/-!
# Soundness of a cell and of the loop over cells

`cellV_mem`: if `pw ∋ A`, `P ∋ e^{−πa}`, `P' ∋ e^{−π(a + a/8)}` and `X` is within `R_d · I_0` of
`A Σ_k choose(z, k) a^{−k} I_k`, then the cell interval encloses `X`.

`loopJ_mem`: after `j` steps the loop encloses `Σ_{i<j} X_{m,i}` (m = 1, 2, 3), `ρ^j` and `e^{−π a_j}`.
AUTHORITY_EFFECT = NONE.
-/

open Complex

namespace AEGIS.RHCheckLoopV1

open AEGIS.RHFixIntervalV1 AEGIS.RHExpEnclosureV1 AEGIS.RHLambdaCheckV1 AEGIS.RHCellBinomialV1
  AEGIS.RHCellMomentsV1 AEGIS.RHCheckSoundV1

variable (p : ℕ)

lemma invAlpha_lo (m : ℕ) : (invAlpha p m).lo = (ofQ p (1 / (piHi * m ^ 2))).lo := by
  unfold invAlpha; rfl

lemma invAlpha_hi (m : ℕ) : (invAlpha p m).hi = (ofQ p (1 / (piLo * m ^ 2))).hi := by
  unfold invAlpha; rfl

theorem invAlpha_mem {m : ℕ} (hm : 1 ≤ m) : (invAlpha p m).Mem p (Real.pi * m ^ 2)⁻¹ := by
  have hm' : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have hlo : (0 : ℝ) < (piLo : ℝ) := by norm_num [piLo]
  constructor
  · rw [invAlpha_lo]
    have h2 : (((1 / (piHi * m ^ 2) : ℚ)) : ℝ) ≤ (Real.pi * m ^ 2)⁻¹ := by
      push_cast
      rw [one_div]
      exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_right le_piHi hm'.le)
    exact (mem_ofQ p _).1.trans h2
  · rw [invAlpha_hi]
    have h2 : (Real.pi * m ^ 2)⁻¹ ≤ (((1 / (piLo * m ^ 2) : ℚ)) : ℝ) := by
      push_cast
      rw [one_div]
      exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_right piLo_le hm'.le)
    exact h2.trans (mem_ofQ p _).2

lemma remQ_nonneg {M : ℚ} {d : ℕ} (hM : 0 ≤ M) (hq : (1 / 8 : ℚ) * (M + d + 1) / (d + 2) < 1) :
    0 ≤ remQ M d (1 / 8) := by
  have hb : 0 ≤ betaQ M (d + 1) := by
    have h := beta_nonneg (M := (M : ℝ)) (by exact_mod_cast hM) (d + 1)
    rw [← betaQ_cast] at h; exact_mod_cast h
  unfold remQ
  have : 0 < 1 - (1 / 8 : ℚ) * (M + d + 1) / (d + 2) := by linarith
  positivity

/-- **One cell.** -/
theorem cellV_mem (zr zi : ℚ) (d : ℕ) (M : ℚ) (hM : 0 ≤ M)
    (hq : (1 / 8 : ℚ) * (M + d + 1) / (d + 2) < 1) {pw : CIv} {A : ℂ} (hpw : CMem p pw A)
    {a : ℚ} (ha : 0 < a) {P P' : Iv} (hP : P.Mem p (Real.exp (-(Real.pi * a))))
    (hP' : P'.Mem p (Real.exp (-(Real.pi * ((a + a / 8 : ℚ) : ℝ))))) {m : ℕ} (hm : 1 ≤ m) {X : ℂ}
    (hX : ‖X - A * ∑ k ∈ Finset.range (d + 1), Ring.choose (zC zr zi) k * (((a : ℝ)⁻¹ ^ k : ℝ) : ℂ) *
        ((mom (Real.pi * m ^ 2) a ((a + a / 8 : ℚ) : ℝ) k : ℝ) : ℂ)‖ ≤
      ((remQ M d (1 / 8) : ℚ) : ℝ) * mom (Real.pi * m ^ 2) a ((a + a / 8 : ℚ) : ℝ) 0) :
    CMem p (cellV p zr zi d (remQ M d (1 / 8)) pw a P P' m) X := by
  set α : ℝ := Real.pi * m ^ 2 with hαdef
  have hα : α ≠ 0 := by positivity
  have hEa : (powIv p P (m ^ 2)).Mem p (Real.exp (-α * a)) := by
    have := mem_powIv p hP (m ^ 2)
    rw [← exp_neg_pi_sq] at this
    exact Mem.congr p this (by rw [hαdef]; ring_nf)
  have hEb : (powIv p P' (m ^ 2)).Mem p (Real.exp (-α * ((a + a / 8 : ℚ) : ℝ))) := by
    have := mem_powIv p hP' (m ^ 2)
    rw [← exp_neg_pi_sq] at this
    exact Mem.congr p this (by rw [hαdef]; ring_nf)
  have hinv : (invAlpha p m).Mem p α⁻¹ := invAlpha_mem p hm
  set I0 := (isub (powIv p P (m ^ 2)) (powIv p P' (m ^ 2))).mul p (invAlpha p m) with hI0def
  have hI0 : I0.Mem p (mom α a ((a + a / 8 : ℚ) : ℝ) 0) := by
    have := Iv.mem_mul p (mem_isub p hEa hEb) hinv
    refine Mem.congr p this ?_
    have e := mom_zero α a ((a + a / 8 : ℚ) : ℝ)
    rw [← e, mul_comm α, mul_inv_cancel_right₀ hα]
  have hc := (cellAux_mem p zr zi a⁻¹ a (a / 8) hα hinv hEb hI0 (d + 1)).1
  have hprod := mem_cmul p hpw hc
  have hR := remQ_nonneg hM hq
  unfold cellV
  rw [← hI0def]
  refine mem_cwiden p hprod ?_
  have hsum : A * ∑ i ∈ Finset.range (d + 1), ((mom α a ((a + a / 8 : ℚ) : ℝ) i : ℝ) : ℂ) *
      (Ring.choose (zC zr zi) i * (((a⁻¹ : ℚ) : ℝ) : ℂ) ^ i) =
      A * ∑ k ∈ Finset.range (d + 1), Ring.choose (zC zr zi) k * (((a : ℝ)⁻¹ ^ k : ℝ) : ℂ) *
        ((mom α a ((a + a / 8 : ℚ) : ℝ) k : ℝ) : ℂ) := by
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast; ring
  rw [hsum]
  refine hX.trans ?_
  have hm0 : mom α a ((a + a / 8 : ℚ) : ℝ) 0 ≤ (I0.hi : ℝ) / 2 ^ p := hI0.2
  calc ((remQ M d (1 / 8) : ℚ) : ℝ) * mom α a ((a + a / 8 : ℚ) : ℝ) 0
      ≤ ((remQ M d (1 / 8) : ℚ) : ℝ) * ((I0.hi : ℝ) / 2 ^ p) :=
        mul_le_mul_of_nonneg_left hm0 (by exact_mod_cast hR)
    _ = (((remQ M d (1 / 8) * I0.hi : ℚ)) : ℝ) / 2 ^ p := by push_cast; ring
    _ ≤ ((⌈remQ M d (1 / 8) * I0.hi⌉ : ℤ) : ℝ) / 2 ^ p := by
        gcongr
        exact_mod_cast Int.le_ceil _

/-- The loop state after `j` cells. -/
def Inv (zr zi : ℚ) (d s N : ℕ) (Rd : ℚ) (ρ : CIv) (ρv : ℂ) (X : ℕ → ℕ → ℂ) (j : ℕ) : Prop :=
  CMem p (loopJ p zr zi d s N Rd ρ j).1 (∑ i ∈ Finset.range j, X 1 i) ∧
  CMem p (loopJ p zr zi d s N Rd ρ j).2.1 (∑ i ∈ Finset.range j, X 2 i) ∧
  CMem p (loopJ p zr zi d s N Rd ρ j).2.2.1 (∑ i ∈ Finset.range j, X 3 i) ∧
  CMem p (loopJ p zr zi d s N Rd ρ j).2.2.2.1 (ρv ^ j) ∧
  (loopJ p zr zi d s N Rd ρ j).2.2.2.2.Mem p (Real.exp (-(Real.pi * (((9 / 8 : ℚ) ^ j : ℚ) : ℝ))))

/-- **The loop.** -/
theorem loopJ_mem (zr zi : ℚ) (d s N : ℕ) (Rd : ℚ) {ρ : CIv} {ρv : ℂ} (hρ : CMem p ρ ρv)
    (X : ℕ → ℕ → ℂ) (J : ℕ)
    (hexp : ∀ j ≤ J, (expNegPi p ((9 / 8 : ℚ) ^ j) s N).Mem p
      (Real.exp (-(Real.pi * (((9 / 8 : ℚ) ^ j : ℚ) : ℝ)))))
    (hcell : ∀ i < J, ∀ m ∈ ({1, 2, 3} : Finset ℕ), ∀ {pw : CIv} {P P' : Iv},
      CMem p pw (ρv ^ i) → P.Mem p (Real.exp (-(Real.pi * (((9 / 8 : ℚ) ^ i : ℚ) : ℝ)))) →
      P'.Mem p (Real.exp (-(Real.pi * (((9 / 8 : ℚ) ^ (i + 1) : ℚ) : ℝ)))) →
      CMem p (cellV p zr zi d Rd pw ((9 / 8 : ℚ) ^ i) P P' m) (X m i)) :
    ∀ j ≤ J, Inv p zr zi d s N Rd ρ ρv X j
  | 0, _ => by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [loopJ] using mem_cof p 0 0
    · simpa [loopJ] using mem_cof p 0 0
    · simpa [loopJ] using mem_cof p 0 0
    · simpa [loopJ] using mem_cof p 1 0
    · simpa [loopJ] using hexp 0 (Nat.zero_le _)
  | j + 1, hj => by
    obtain ⟨h1, h2, h3, hpw, hP⟩ := loopJ_mem zr zi d s N Rd hρ X J hexp hcell j (by omega)
    have hP' := hexp (j + 1) hj
    have hjJ : j < J := by omega
    rcases hc : loopJ p zr zi d s N Rd ρ j with ⟨S1, S2, S3, pw, P⟩
    simp only [hc] at h1 h2 h3 hpw hP
    unfold Inv
    simp only [loopJ, hc, Finset.sum_range_succ]
    refine ⟨?_, ?_, ?_, ?_, hP'⟩
    · exact mem_cadd p h1 (hcell j hjJ 1 (by simp) hpw hP hP')
    · exact mem_cadd p h2 (hcell j hjJ 2 (by simp) hpw hP hP')
    · exact mem_cadd p h3 (hcell j hjJ 3 (by simp) hpw hP hP')
    · rw [pow_succ]; exact mem_cmul p hpw hρ

end AEGIS.RHCheckLoopV1

#print axioms AEGIS.RHCheckLoopV1.cellV_mem
#print axioms AEGIS.RHCheckLoopV1.loopJ_mem
