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

import RHFixIntervalV1
import RHPi80V1

/-!
# Fixed-point enclosures of `e^{−q}` and `e^{−πa}`

* `ofQ q`, `ball q e`: the integer interval around a rational (outward rounding).
* `expQ x N`: Taylor sum of `e^x` in `ℚ` plus the Lagrange bound of `Real.exp_bound` (`|x| ≤ 1`).
* `expNegQ q s N`: `e^{−q} = (e^{−q/2^s})^{2^s}`, `s` squarings (`0 ≤ q ≤ 2^s`).
* `expNegPi a`: `e^{−πa}` from `π` to eighty digits (`RHPi80V1`, Mathlib's `sqrtTwoAddSeries` chain).
* `powIv k I`: `I^k`; with it `e^{−π m² a} = (e^{−πa})^{m²}` reuses one exponential.

All of it is integer and rational arithmetic, so the kernel evaluates it.  AUTHORITY_EFFECT = NONE.
-/

namespace AEGIS.RHExpEnclosureV1

open AEGIS.RHFixIntervalV1

variable (p : ℕ)

/-- The integer interval around a rational. -/
def ofQ (q : ℚ) : Iv := ⟨⌊q * 2 ^ p⌋, ⌈q * 2 ^ p⌉⟩

/-- The integer interval around `[q − e, q + e]`. -/
def ball (q e : ℚ) : Iv := ⟨⌊(q - e) * 2 ^ p⌋, ⌈(q + e) * 2 ^ p⌉⟩

lemma floor_le_real (q : ℚ) : ((⌊q * 2 ^ p⌋ : ℤ) : ℝ) / 2 ^ p ≤ (q : ℝ) := by
  rw [div_le_iff₀ (two_pow_pos p)]
  have h : ((⌊q * 2 ^ p⌋ : ℤ) : ℚ) ≤ q * 2 ^ p := Int.floor_le _
  exact_mod_cast h

lemma real_le_ceil (q : ℚ) : (q : ℝ) ≤ ((⌈q * 2 ^ p⌉ : ℤ) : ℝ) / 2 ^ p := by
  rw [le_div_iff₀ (two_pow_pos p)]
  have h : q * 2 ^ p ≤ ((⌈q * 2 ^ p⌉ : ℤ) : ℚ) := Int.le_ceil _
  exact_mod_cast h

theorem mem_ofQ (q : ℚ) : (ofQ p q).Mem p (q : ℝ) := ⟨floor_le_real p q, real_le_ceil p q⟩

theorem mem_ball {x : ℝ} {q e : ℚ} (h : |x - q| ≤ e) : (ball p q e).Mem p x := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor
  · refine (floor_le_real p (q - e)).trans ?_
    push_cast; linarith
  · refine le_trans ?_ (real_le_ceil p (q + e))
    push_cast; linarith

/-- `(Σ_{i<n} x^i/i!, x^n/n!)`. -/
def taylorAux (x : ℚ) : ℕ → ℚ × ℚ
  | 0 => (0, 1)
  | n + 1 => match taylorAux x n with
    | (s, t) => (s + t, t * x / (n + 1))

theorem taylorAux_eq (x : ℚ) : ∀ n, taylorAux x n =
    (∑ i ∈ Finset.range n, x ^ i / (i.factorial : ℚ), x ^ n / (n.factorial : ℚ))
  | 0 => by simp [taylorAux]
  | n + 1 => by
    rw [taylorAux, taylorAux_eq x n]
    simp only [Finset.sum_range_succ, Prod.mk.injEq, true_and, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, pow_succ]
    have : ((n.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp

/-- `e^x` for `|x| ≤ 1`: Taylor sum plus `|x|^N (N+1)/(N! N)`. -/
def expQ (x : ℚ) (N : ℕ) : Iv :=
  ball p (taylorAux x N).1 (|x| ^ N * ((N + 1 : ℚ) / ((N.factorial : ℚ) * N)))

theorem mem_expQ {x : ℚ} (hx : |x| ≤ 1) {N : ℕ} (hN : 0 < N) : (expQ p x N).Mem p (Real.exp x) := by
  refine mem_ball p ?_
  have hx' : |(x : ℝ)| ≤ 1 := by exact_mod_cast hx
  have h := Real.exp_bound hx' hN
  rw [taylorAux_eq]
  push_cast
  simpa [Nat.succ_eq_add_one] using h

/-- `s` squarings. -/
def sqN : ℕ → Iv → Iv
  | 0, I => I
  | k + 1, I => sqN k (I.mul p I)

theorem mem_sqN : ∀ (k : ℕ) {I : Iv} {v : ℝ}, I.Mem p v → (sqN p k I).Mem p (v ^ (2 ^ k))
  | 0, _, _, h => by simpa [sqN] using h
  | k + 1, _, v, h => by
    have := mem_sqN k (Iv.mem_mul p h h)
    rw [sqN]
    rwa [← sq, ← pow_mul, ← pow_succ'] at this

/-- `e^{−q} = (e^{−q/2^s})^{2^s}`. -/
def expNegQ (q : ℚ) (s N : ℕ) : Iv := sqN p s (expQ p (-q / 2 ^ s) N)

theorem mem_expNegQ {q : ℚ} {s N : ℕ} (hq0 : 0 ≤ q) (hq : q ≤ 2 ^ s) (hN : 0 < N) :
    (expNegQ p q s N).Mem p (Real.exp (-q)) := by
  have hx : |-q / 2 ^ s| ≤ 1 := by
    rw [abs_div, abs_neg, abs_of_nonneg hq0, abs_of_pos (by positivity), div_le_one (by positivity)]
    exact hq
  have h := mem_sqN p s (mem_expQ p hx hN)
  have e : Real.exp (-q) = Real.exp (((-q / 2 ^ s : ℚ) : ℝ)) ^ (2 ^ s) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
  rw [e]; exact h

/-- Eighty digits of `π` (`RHPi80V1`). -/
def piLo : ℚ := 314159265358979323846264338327950288419716939937510582097494459230781640628620899 / 10 ^ 80
def piHi : ℚ := 314159265358979323846264338327950288419716939937510582097494459230781640628620900 / 10 ^ 80

theorem piLo_le : (piLo : ℝ) ≤ Real.pi := by
  have h := AEGIS.RHPi80V1.pi_gt_d80
  simp only [piLo]; push_cast; linarith

theorem le_piHi : Real.pi ≤ (piHi : ℝ) := by
  have h := AEGIS.RHPi80V1.pi_lt_d80
  simp only [piHi]; push_cast; linarith

/-- `e^{−πa}` for `a ≥ 0`, monotone in `π`. -/
def expNegPi (a : ℚ) (s N : ℕ) : Iv :=
  ⟨(expNegQ p (piHi * a) s N).lo, (expNegQ p (piLo * a) s N).hi⟩

lemma piLo_le_piHi : piLo ≤ piHi := by rw [piLo, piHi]; norm_num

lemma piLo_nonneg : 0 ≤ piLo := by rw [piLo]; norm_num

lemma expNegPi_lo (a : ℚ) (s N : ℕ) : (expNegPi p a s N).lo = (expNegQ p (piHi * a) s N).lo := by
  unfold expNegPi; rfl

lemma expNegPi_hi (a : ℚ) (s N : ℕ) : (expNegPi p a s N).hi = (expNegQ p (piLo * a) s N).hi := by
  unfold expNegPi; rfl

lemma pi_mul_le {a : ℝ} (ha : 0 ≤ a) : Real.pi * a ≤ (piHi : ℝ) * a :=
  mul_le_mul_of_nonneg_right le_piHi ha

lemma le_pi_mul {a : ℝ} (ha : 0 ≤ a) : (piLo : ℝ) * a ≤ Real.pi * a :=
  mul_le_mul_of_nonneg_right piLo_le ha

theorem mem_expNegPi {a : ℚ} {s N : ℕ} (ha : 0 ≤ a) (hs : piHi * a ≤ 2 ^ s) (hN : 0 < N) :
    (expNegPi p a s N).Mem p (Real.exp (-(Real.pi * a))) := by
  have hhi0 : 0 ≤ piHi * a := mul_nonneg (piLo_nonneg.trans piLo_le_piHi) ha
  have hlo0 : 0 ≤ piLo * a := mul_nonneg piLo_nonneg ha
  have hloS : piLo * a ≤ 2 ^ s := le_trans (mul_le_mul_of_nonneg_right piLo_le_piHi ha) hs
  have h1 := (mem_expNegQ p hhi0 hs hN).1
  have h2 := (mem_expNegQ p hlo0 hloS hN).2
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  rw [Rat.cast_mul] at h1 h2
  constructor
  · rw [expNegPi_lo]
    exact h1.trans (Real.exp_le_exp.mpr (neg_le_neg (pi_mul_le ha')))
  · rw [expNegPi_hi]
    exact le_trans (Real.exp_le_exp.mpr (neg_le_neg (le_pi_mul ha'))) h2

/-- `I^k`. -/
def powIv (I : Iv) : ℕ → Iv
  | 0 => ofQ p 1
  | k + 1 => (powIv I k).mul p I

theorem mem_powIv {I : Iv} {v : ℝ} (h : I.Mem p v) : ∀ k, (powIv p I k).Mem p (v ^ k)
  | 0 => by simpa [powIv] using mem_ofQ p 1
  | k + 1 => by rw [powIv, pow_succ]; exact Iv.mem_mul p (mem_powIv h k) h

/-- `e^{−π m² a} = (e^{−πa})^{m²}`. -/
theorem exp_neg_pi_sq (m : ℕ) (a : ℝ) :
    Real.exp (-(Real.pi * m ^ 2 * a)) = Real.exp (-(Real.pi * a)) ^ (m ^ 2) := by
  rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

end AEGIS.RHExpEnclosureV1

#print axioms AEGIS.RHExpEnclosureV1.mem_expNegPi
#print axioms AEGIS.RHExpEnclosureV1.mem_powIv
#print axioms AEGIS.RHExpEnclosureV1.exp_neg_pi_sq
