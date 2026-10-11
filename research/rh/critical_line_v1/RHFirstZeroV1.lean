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

import RHCheckLoopV1
import RHCellSplitV1
import RHMellinThreeTermsV1
import RHLambdaLineV1

/-!
# A zero of `ζ` on the critical line with `14 ≤ t ≤ 14.3`, checked by the kernel

`lamIv_mem`: the integer interval `lamIv p t M d K J s N` contains `re Λ(1/2 + it)` (conditions on
the parameters are rational inequalities).  The kernel evaluates `lamIv` at `t = 14` and `t = 14.3`
(`decide +kernel`): the first interval lies below `0`, the second above.  `Λ(1/2 + it)` is real and
continuous, so `ζ(1/2 + it) = 0` for some `t ∈ [14, 14.3]` (`first_zero`).

This is one zero, found by a sign change. It says nothing about zeros off the line.
AUTHORITY_EFFECT = NONE.
-/

open Complex Set MeasureTheory

namespace AEGIS.RHFirstZeroV1

open AEGIS.RHFixIntervalV1 AEGIS.RHExpEnclosureV1 AEGIS.RHLambdaCheckV1 AEGIS.RHCellBinomialV1
  AEGIS.RHCellMomentsV1 AEGIS.RHCheckSoundV1 AEGIS.RHCheckLoopV1 AEGIS.RHCellSplitV1
  AEGIS.RHCriticalLineSignV1

variable (p : ℕ)

lemma zC_re (zr zi : ℚ) : (zC zr zi).re = zr := by simp [zC]

lemma zC_im (zr zi : ℚ) : (zC zr zi).im = zi := by simp [zC]

lemma norm_zC_le {zr zi M : ℚ} (hM : 0 ≤ M) (h : zr ^ 2 + zi ^ 2 ≤ M ^ 2) :
    ‖zC zr zi‖ ≤ (M : ℝ) := by
  have h2 : ‖zC zr zi‖ ^ 2 ≤ (M : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, zC_re, zC_im]
    have : ((zr : ℝ)) ^ 2 + (zi : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := by exact_mod_cast h
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by exact_mod_cast hM) two_ne_zero).mp h2

lemma line_sub_one (t : ℚ) : lineAt (t : ℝ) / 2 - 1 = zC (-3 / 4) (t / 2) := by
  apply Complex.ext <;> simp [lineAt, zC] <;> norm_num

lemma q_cast {M : ℚ} {d : ℕ} (h : (1 / 8 : ℚ) * (M + d + 1) / (d + 2) < 1) :
    (((1 / 8 : ℚ) : ℝ)) * ((M : ℝ) + d + 1) / (d + 2) < 1 := by
  have : (((1 / 8 * (M + d + 1) / (d + 2) : ℚ)) : ℝ) < 1 := by exact_mod_cast h
  push_cast at this ⊢
  linarith

/-- `ρ = (9/8)^z`. -/
theorem rho_mem (t M : ℚ) (K : ℕ) (hM : 1 ≤ M) (hzM : (-3 / 4 : ℚ) ^ 2 + (t / 2) ^ 2 ≤ M ^ 2)
    (hqK : (1 / 8 : ℚ) * (M + K + 1) / (K + 2) < 1) :
    CMem p (rhoIv p t M K) ((((9 / 8 : ℚ) : ℝ) : ℂ) ^ zC (-3 / 4) (t / 2)) := by
  have hb := (binAux_mem p (-3 / 4) (t / 2) (1 / 8) (K + 1)).1
  refine mem_cwiden p hb ?_
  have hz := norm_zC_le (by linarith) hzM
  have h := binom_rem_le (zC (-3 / 4) (t / 2)) K hz (by exact_mod_cast hM)
    (u := ((1 / 8 : ℚ) : ℝ)) (U := ((1 / 8 : ℚ) : ℝ)) (by norm_num) le_rfl (q_cast hqK)
  have e : (1 + ((((1 / 8 : ℚ) : ℝ)) : ℂ)) = ((((9 / 8 : ℚ) : ℝ)) : ℂ) := by push_cast; norm_num
  rw [e, ← remQ_cast] at h
  exact h.trans (le_ceil_div p _)

theorem hexp_all {J s N : ℕ} (hs : piHi * (9 / 8) ^ J ≤ 2 ^ s) (hN : 0 < N) :
    ∀ j ≤ J, (expNegPi p ((9 / 8 : ℚ) ^ j) s N).Mem p
      (Real.exp (-(Real.pi * (((9 / 8 : ℚ) ^ j : ℚ) : ℝ)))) := by
  intro j hj
  refine mem_expNegPi p (by positivity) (le_trans ?_ hs) hN
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hj) (by norm_num [piHi])

/-- The cell integrals. -/
noncomputable def Xc (z : ℂ) (m j : ℕ) : ℂ := ∫ x in aj j..aj (j + 1), f z (Real.pi * m ^ 2) x

theorem hcell_all (t M : ℚ) (d J : ℕ) (hM : 1 ≤ M) (hzM : (-3 / 4 : ℚ) ^ 2 + (t / 2) ^ 2 ≤ M ^ 2)
    (hqd : (1 / 8 : ℚ) * (M + d + 1) / (d + 2) < 1) :
    ∀ i < J, ∀ m ∈ ({1, 2, 3} : Finset ℕ), ∀ {pw : CIv} {P P' : Iv},
      CMem p pw (((((9 / 8 : ℚ) : ℝ) : ℂ) ^ zC (-3 / 4) (t / 2)) ^ i) →
      P.Mem p (Real.exp (-(Real.pi * (((9 / 8 : ℚ) ^ i : ℚ) : ℝ)))) →
      P'.Mem p (Real.exp (-(Real.pi * (((9 / 8 : ℚ) ^ (i + 1) : ℚ) : ℝ)))) →
      CMem p (cellV p (-3 / 4) (t / 2) d (remQ M d (1 / 8)) pw ((9 / 8 : ℚ) ^ i) P P' m)
        (Xc (zC (-3 / 4) (t / 2)) m i) := by
  intro i _ m hm pw P P' hpw hP hP'
  set z := zC (-3 / 4) (t / 2) with hzdef
  have hm1 : 1 ≤ m := by simp at hm; omega
  set a : ℚ := (9 / 8 : ℚ) ^ i with hadef
  have hab : (9 / 8 : ℚ) ^ (i + 1) = a + a / 8 := by rw [hadef]; ring
  rw [hab] at hP'
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by rw [hadef]; push_cast; exact one_le_pow₀ (by norm_num)
  have hzre : z.re ≤ 0 := by rw [hzdef, zC_re]; norm_num
  have hz := norm_zC_le (by linarith) hzM
  have hb : ((a + a / 8 : ℚ) : ℝ) = (a : ℝ) + (a : ℝ) / 8 := by push_cast; ring
  have hle : (a : ℝ) ≤ ((a + a / 8 : ℚ) : ℝ) := by rw [hb]; linarith
  have hU : (((a + a / 8 : ℚ) : ℝ) - a) / a ≤ ((1 / 8 : ℚ) : ℝ) := by
    have ha0 : (a : ℝ) ≠ 0 := by linarith
    rw [hb, show (a : ℝ) + a / 8 - a = a / 8 by ring, div_div_cancel_left' ha0]
    norm_num
  have hc := cell_approx (α := Real.pi * m ^ 2) ha1 hle hzre d hz (by exact_mod_cast hM) hU (q_cast hqd)
  rw [← remQ_cast] at hc
  have hA : ((a : ℝ) : ℂ) ^ z = ((((9 / 8 : ℚ) : ℝ) : ℂ) ^ z) ^ i := by
    rw [← cpow_geom (by norm_num) z i, hadef]; norm_cast
  rw [hA] at hc
  have hX : Xc z m i = ∫ x in (a : ℝ)..((a + a / 8 : ℚ) : ℝ),
      (x : ℂ) ^ z * ((Real.exp (-(Real.pi * m ^ 2) * x) : ℝ) : ℂ) := by
    rw [Xc, show aj (i + 1) = ((a + a / 8 : ℚ) : ℝ) by rw [aj, hab]]
    rfl
  rw [hX]
  exact cellV_mem p (-3 / 4) (t / 2) d M (by linarith) hqd hpw (a := a) (by rw [hadef]; positivity)
    hP hP' hm1 hc

/-- The tail beyond `X` for `α = π m²`, in units of `2^{-p}`. -/
theorem tail_units {m : ℕ} (hm : 1 ≤ m) {PJ : Iv} {X : ℝ}
    (hPJ : PJ.Mem p (Real.exp (-(Real.pi * X)))) :
    Real.exp (-(Real.pi * m ^ 2) * X) / (Real.pi * m ^ 2) ≤
      ((⌈((powIv p PJ (m ^ 2)).hi * (invAlpha p m).hi : ℚ) / 2 ^ p⌉ : ℤ) : ℝ) / 2 ^ p := by
  have hE := mem_powIv p hPJ (m ^ 2)
  rw [← exp_neg_pi_sq] at hE
  have he : Real.exp (-(Real.pi * m ^ 2) * X) = Real.exp (-(Real.pi * m ^ 2 * X)) := by ring_nf
  have hinv := invAlpha_mem p hm
  have hp := two_pow_pos p
  rw [he, div_eq_mul_inv]
  calc Real.exp (-(Real.pi * m ^ 2 * X)) * (Real.pi * m ^ 2)⁻¹
      ≤ (((powIv p PJ (m ^ 2)).hi : ℝ) / 2 ^ p) * (((invAlpha p m).hi : ℝ) / 2 ^ p) :=
        mul_le_mul hE.2 hinv.2 (by positivity) ((Real.exp_pos _).le.trans hE.2)
    _ = ((((powIv p PJ (m ^ 2)).hi * (invAlpha p m).hi : ℚ) / 2 ^ p : ℚ) : ℝ) / 2 ^ p := by
        push_cast; ring
    _ ≤ _ := by
        gcongr
        exact_mod_cast Int.le_ceil _

/-- The three-term error in units of `2^{-p}`. -/
theorem eps_units {P0 : Iv} (hP0 : P0.Mem p (Real.exp (-(Real.pi * ((1 : ℚ) : ℝ))))) :
    4 * Real.exp (-16 * Real.pi) / (16 * Real.pi) ≤
      ((⌈(P0.hi : ℚ) ^ 16 / 2 ^ (15 * p)⌉ : ℤ) : ℝ) / 2 ^ p := by
  have hpi := Real.pi_gt_three
  have hp := two_pow_pos p
  rw [Rat.cast_one, mul_one] at hP0
  have h1 : 4 * Real.exp (-16 * Real.pi) / (16 * Real.pi) ≤ Real.exp (-16 * Real.pi) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.exp_pos (-16 * Real.pi)]
  have h2 : Real.exp (-16 * Real.pi) = Real.exp (-Real.pi) ^ 16 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h3 : Real.exp (-Real.pi) ^ 16 ≤ ((P0.hi : ℝ) / 2 ^ p) ^ 16 :=
    pow_le_pow_left₀ (Real.exp_pos _).le hP0.2 16
  have h4 : ((P0.hi : ℝ) / 2 ^ p) ^ 16 = (((P0.hi : ℚ) ^ 16 / 2 ^ (15 * p) : ℚ) : ℝ) / 2 ^ p := by
    push_cast
    rw [div_pow, div_div, ← pow_mul, ← pow_add]
    congr 2; ring
  calc 4 * Real.exp (-16 * Real.pi) / (16 * Real.pi) ≤ ((P0.hi : ℝ) / 2 ^ p) ^ 16 := by
        rw [← h2] at h3; exact h1.trans h3
    _ = _ := h4
    _ ≤ _ := by
        gcongr
        exact_mod_cast Int.le_ceil _

/-- `G n w` as the integral of `f`. -/
lemma G_eq (t : ℚ) (n : ℕ) :
    AEGIS.RHMellinThreeTermsV1.G n (lineAt (t : ℝ) / 2) =
      ∫ x in Ioi (1 : ℝ), f (zC (-3 / 4) (t / 2)) (Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) x := by
  rw [AEGIS.RHMellinThreeTermsV1.G]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [f, line_sub_one]
  congr 3
  push_cast; ring

/-- **The enclosure contains `re Λ(1/2 + it)`.** -/
theorem lamIv_mem (t M : ℚ) (d K J s N : ℕ) (hM : 1 ≤ M)
    (hzM : (-3 / 4 : ℚ) ^ 2 + (t / 2) ^ 2 ≤ M ^ 2) (hqK : (1 / 8 : ℚ) * (M + K + 1) / (K + 2) < 1)
    (hqd : (1 / 8 : ℚ) * (M + d + 1) / (d + 2) < 1) (hs : piHi * (9 / 8) ^ J ≤ 2 ^ s) (hN : 0 < N) :
    (lamIv p t M d K J s N).Mem p (Xi (t : ℝ)).re := by
  set z := zC (-3 / 4) (t / 2) with hzdef
  have hzre : z.re ≤ 0 := by rw [hzdef, zC_re]; norm_num
  have hloop := loopJ_mem p (-3 / 4) (t / 2) d s N (remQ M d (1 / 8)) (rho_mem p t M K hM hzM hqK)
    (Xc z) J (hexp_all p hs hN) (hcell_all p t M d J hM hzM hqd) J le_rfl
  unfold AEGIS.RHCheckLoopV1.Inv at hloop
  have hP0 := mem_expNegPi p (a := 1) (s := s) (N := N) (by norm_num)
    (le_trans (mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 9 / 8))
      (by norm_num [piHi])) hs) hN
  unfold lamIv
  rcases hl : loopJ p (-3 / 4) (t / 2) d s N (remQ M d (1 / 8)) (rhoIv p t M K) J with
    ⟨S1, S2, S3, pw, PJ⟩
  rw [hl] at hloop
  obtain ⟨h1, h2, h3, -, hPJ⟩ := hloop
  rw [lamCore, RHLambdaLineV1.Xi_re_eq]
  set w := lineAt (t : ℝ) / 2 with hwdef
  set T := ∑ i ∈ Finset.range J, Xc z 1 i + ∑ i ∈ Finset.range J, Xc z 2 i +
    ∑ i ∈ Finset.range J, Xc z 3 i with hT
  simp only at h1 h2 h3 hPJ
  have htot := mem_cadd p (mem_cadd p h1 h2) h3
  rw [← hT] at htot
  suffices hbudget : |(mellin AEGIS.RHRiemannThetaFormulaV1.A w).re - ((2 : ℚ) : ℝ) * T.re| ≤
      ((tailW p PJ (expNegPi p 1 s N) : ℤ) : ℝ) / 2 ^ p by
    have hin := mem_iwiden p (x := (mellin AEGIS.RHRiemannThetaFormulaV1.A w).re)
      (Iv.mem_mul p (mem_ofQ p 2) htot.1) hbudget
    exact Mem.congr p (mem_isub p hin (mem_ofQ p (1 / (1 / 4 + t ^ 2)))) (by push_cast; ring)
  -- the error budget
  have hw : w.re ≤ 1 := by rw [hwdef]; simp [lineAt]; norm_num
  have h3t := AEGIS.RHMellinThreeTermsV1.mellin_A_three_terms hw
  have hsplit : ∀ n : ℕ, AEGIS.RHMellinThreeTermsV1.G n w =
      ∑ i ∈ Finset.range J, Xc z (n + 1) i +
        ∫ x in Ioi (aj J), f z (Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) x := by
    intro n
    rw [hwdef, G_eq, split_cells (by positivity) hzre J]
    rfl
  have htail : ∀ n : ℕ, ‖∫ x in Ioi (aj J), f z (Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) x‖ ≤
      ((⌈((powIv p PJ ((n + 1) ^ 2)).hi * (invAlpha p (n + 1)).hi : ℚ) / 2 ^ p⌉ : ℤ) : ℝ) /
        2 ^ p := by
    intro n
    refine (tail_le (by positivity) (one_le_aj J) hzre).trans ?_
    exact tail_units p (by omega) (X := aj J) hPJ
  have hG : ∑ n ∈ Finset.range 3, 2 * AEGIS.RHMellinThreeTermsV1.G n w =
      2 * T + 2 * ((∫ x in Ioi (aj J), f z (Real.pi * ((1 : ℕ) : ℝ) ^ 2) x) +
        (∫ x in Ioi (aj J), f z (Real.pi * ((2 : ℕ) : ℝ) ^ 2) x) +
        (∫ x in Ioi (aj J), f z (Real.pi * ((3 : ℕ) : ℝ) ^ 2) x)) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hsplit, hT, zero_add, Nat.reduceAdd]
    ring
  have ht1 := htail 0
  have ht2 := htail 1
  have ht3 := htail 2
  simp only [zero_add, Nat.reduceAdd] at ht1 ht2 ht3
  have he := eps_units p hP0
  have hre : |(mellin AEGIS.RHRiemannThetaFormulaV1.A w).re - ((2 : ℚ) : ℝ) * T.re| ≤
      ‖mellin AEGIS.RHRiemannThetaFormulaV1.A w - 2 * T‖ := by
    refine le_of_eq_of_le ?_ (abs_re_le_norm _)
    simp [Complex.sub_re, Complex.mul_re]
  refine hre.trans ?_
  have hkey : mellin AEGIS.RHRiemannThetaFormulaV1.A w - 2 * T =
      (mellin AEGIS.RHRiemannThetaFormulaV1.A w -
        ∑ n ∈ Finset.range 3, 2 * AEGIS.RHMellinThreeTermsV1.G n w) +
      2 * ((∫ x in Ioi (aj J), f z (Real.pi * ((1 : ℕ) : ℝ) ^ 2) x) +
        (∫ x in Ioi (aj J), f z (Real.pi * ((2 : ℕ) : ℝ) ^ 2) x) +
        (∫ x in Ioi (aj J), f z (Real.pi * ((3 : ℕ) : ℝ) ^ 2) x)) := by
    rw [hG]; ring
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [hkey]
  calc _ ≤ ‖mellin AEGIS.RHRiemannThetaFormulaV1.A w -
          ∑ n ∈ Finset.range 3, 2 * AEGIS.RHMellinThreeTermsV1.G n w‖ +
        2 * (‖∫ x in Ioi (aj J), f z (Real.pi * ((1 : ℕ) : ℝ) ^ 2) x‖ +
          ‖∫ x in Ioi (aj J), f z (Real.pi * ((2 : ℕ) : ℝ) ^ 2) x‖ +
          ‖∫ x in Ioi (aj J), f z (Real.pi * ((3 : ℕ) : ℝ) ^ 2) x‖) := by
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_mul, h2]
        gcongr
        exact norm_add₃_le
    _ ≤ ((tailW p PJ (expNegPi p 1 s N) : ℤ) : ℝ) / 2 ^ p := by
        have hW : ((tailW p PJ (expNegPi p 1 s N) : ℤ) : ℝ) / 2 ^ p =
            2 * (((⌈((powIv p PJ (1 ^ 2)).hi * (invAlpha p 1).hi : ℚ) / 2 ^ p⌉ : ℤ) : ℝ) / 2 ^ p +
                 ((⌈((powIv p PJ (2 ^ 2)).hi * (invAlpha p 2).hi : ℚ) / 2 ^ p⌉ : ℤ) : ℝ) / 2 ^ p +
                 ((⌈((powIv p PJ (3 ^ 2)).hi * (invAlpha p 3).hi : ℚ) / 2 ^ p⌉ : ℤ) : ℝ) / 2 ^ p) +
            ((⌈((expNegPi p 1 s N).hi : ℚ) ^ 16 / 2 ^ (15 * p)⌉ : ℤ) : ℝ) / 2 ^ p := by
          rw [tailW]; push_cast; ring
        rw [hW]
        linarith [h3t.trans he]


/-- The kernel evaluates the enclosure at `t = 14`: it lies below `0`. -/
theorem lam14_neg : (lamIv 128 14 (15 / 2) 14 50 22 6 30).hi < 0 := by decide +kernel

/-- The kernel evaluates the enclosure at `t = 14.3`: it lies above `0`. -/
theorem lam143_pos : 0 < (lamIv 128 (143 / 10) (15 / 2) 14 50 22 6 30).lo := by decide +kernel

theorem Xi14_neg : (Xi 14).re < 0 := by
  have h := (lamIv_mem 128 14 (15 / 2) 14 50 22 6 30 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [piHi]) (by norm_num)).2
  have hneg : ((lamIv 128 14 (15 / 2) 14 50 22 6 30).hi : ℝ) / 2 ^ 128 < 0 :=
    div_neg_of_neg_of_pos (by exact_mod_cast lam14_neg) (by positivity)
  have e : ((14 : ℚ) : ℝ) = 14 := by norm_num
  rw [e] at h
  linarith

theorem Xi143_pos : 0 < (Xi (143 / 10)).re := by
  have h := (lamIv_mem 128 (143 / 10) (15 / 2) 14 50 22 6 30 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [piHi]) (by norm_num)).1
  have hpos : 0 < ((lamIv 128 (143 / 10) (15 / 2) 14 50 22 6 30).lo : ℝ) / 2 ^ 128 :=
    div_pos (by exact_mod_cast lam143_pos) (by positivity)
  have e : ((143 / 10 : ℚ) : ℝ) = 143 / 10 := by norm_num
  rw [e] at h
  linarith

/-- **A zero of `ζ` on the critical line with `14 ≤ t ≤ 14.3`.** -/
theorem first_zero : ∃ t ∈ Set.Icc (14 : ℝ) (143 / 10), riemannZeta (1 / 2 + t * I) = 0 :=
  exists_zero_of_sign_change (by norm_num) (Or.inl ⟨Xi14_neg.le, Xi143_pos.le⟩)

end AEGIS.RHFirstZeroV1

#print axioms AEGIS.RHFirstZeroV1.lamIv_mem
#print axioms AEGIS.RHFirstZeroV1.lam14_neg
#print axioms AEGIS.RHFirstZeroV1.lam143_pos
#print axioms AEGIS.RHFirstZeroV1.first_zero
