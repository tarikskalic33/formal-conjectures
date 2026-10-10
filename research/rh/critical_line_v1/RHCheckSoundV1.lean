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

import RHLambdaCheckV1
import RHCellMomentsV1

/-!
# Soundness of the checker's operations

`CMem p C v`: the complex interval `C` encloses `v`.  Each operation of `RHLambdaCheckV1` is sound,
the binomial recursion `binAux` encloses `Σ_{i<k} choose(z, i) u^i` and `choose(z, k) u^k`, and
`cellAux` encloses the coefficients `choose(z, k) ainv^k`, the moments `I_k` and `Σ_{i<k} I_i T_i`.
AUTHORITY_EFFECT = NONE.
-/

open Complex

namespace AEGIS.RHCheckSoundV1

open AEGIS.RHFixIntervalV1 AEGIS.RHExpEnclosureV1 AEGIS.RHLambdaCheckV1 AEGIS.RHCellBinomialV1
  AEGIS.RHCellMomentsV1

variable (p : ℕ)

/-- `C` encloses `v`. -/
def CMem (C : CIv) (v : ℂ) : Prop := C.re.Mem p v.re ∧ C.im.Mem p v.im

lemma Mem.congr {I : Iv} {x y : ℝ} (h : I.Mem p x) (e : x = y) : I.Mem p y := e ▸ h

lemma CMem.congr {C : CIv} {v w : ℂ} (h : CMem p C v) (e : v = w) : CMem p C w := e ▸ h

lemma mem_isub {I J : Iv} {x y : ℝ} (hx : I.Mem p x) (hy : J.Mem p y) : (isub I J).Mem p (x - y) := by
  rw [sub_eq_add_neg]; exact Iv.mem_add p hx (Iv.mem_neg p hy)

lemma mem_iwiden {I : Iv} {x y : ℝ} {e : ℤ} (hy : I.Mem p y) (h : |x - y| ≤ (e : ℝ) / 2 ^ p) :
    (iwiden I e).Mem p x := by
  obtain ⟨h1, h2⟩ := hy
  obtain ⟨h3, h4⟩ := abs_le.mp h
  constructor <;> simp only [iwiden, Int.cast_sub, Int.cast_add, sub_div, add_div] <;> linarith

lemma mem_cof (x y : ℚ) : CMem p (cof p x y) (((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I) :=
  ⟨by simpa [cof] using mem_ofQ p x, by simpa [cof] using mem_ofQ p y⟩

lemma mem_cadd {C D : CIv} {v w : ℂ} (hv : CMem p C v) (hw : CMem p D w) :
    CMem p (cadd C D) (v + w) :=
  ⟨by simpa [cadd] using Iv.mem_add p hv.1 hw.1, by simpa [cadd] using Iv.mem_add p hv.2 hw.2⟩

lemma mem_cmul {C D : CIv} {v w : ℂ} (hv : CMem p C v) (hw : CMem p D w) :
    CMem p (cmul p C D) (v * w) :=
  ⟨by simpa [cmul, Complex.mul_re] using mem_isub p (Iv.mem_mul p hv.1 hw.1) (Iv.mem_mul p hv.2 hw.2),
   by simpa [cmul, Complex.mul_im] using Iv.mem_add p (Iv.mem_mul p hv.1 hw.2) (Iv.mem_mul p hv.2 hw.1)⟩

lemma mem_csmul {I : Iv} {C : CIv} {r : ℝ} {v : ℂ} (hr : I.Mem p r) (hv : CMem p C v) :
    CMem p (csmul p I C) ((r : ℂ) * v) :=
  ⟨by simpa [csmul] using Iv.mem_mul p hr hv.1, by simpa [csmul] using Iv.mem_mul p hr hv.2⟩

lemma mem_cwiden {C : CIv} {u v : ℂ} {e : ℤ} (hv : CMem p C v) (h : ‖u - v‖ ≤ (e : ℝ) / 2 ^ p) :
    CMem p (cwiden C e) u :=
  ⟨mem_iwiden p hv.1 (by simpa using (abs_re_le_norm (u - v)).trans h),
   mem_iwiden p hv.2 (by simpa using (abs_im_le_norm (u - v)).trans h)⟩

/-- `x ≤ ⌈x 2^p⌉ / 2^p`. -/
lemma le_ceil_div (x : ℚ) : (x : ℝ) ≤ ((⌈x * 2 ^ p⌉ : ℤ) : ℝ) / 2 ^ p := real_le_ceil p x

/-- `z = zr + zi i`. -/
noncomputable def zC (zr zi : ℚ) : ℂ := ((zr : ℝ) : ℂ) + ((zi : ℝ) : ℂ) * I

lemma cof_sub (zr zi : ℚ) (k : ℕ) :
    (((zr - k : ℚ) : ℝ) : ℂ) + ((zi : ℝ) : ℂ) * I = zC zr zi - k := by
  simp only [zC]; push_cast; ring

/-- The binomial terms step: `choose(z, k+1) u^{k+1} = (u/(k+1)) (choose(z, k) u^k (z − k))`. -/
lemma bin_step (z : ℂ) (u : ℚ) (k : ℕ) :
    (((u / (k + 1) : ℚ) : ℝ) : ℂ) * (Ring.choose z k * ((u : ℝ) : ℂ) ^ k * (z - k)) =
      Ring.choose z (k + 1) * ((u : ℝ) : ℂ) ^ (k + 1) := by
  rw [choose_succ]
  have h : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  push_cast
  field_simp
  ring

theorem binAux_mem (zr zi u : ℚ) : ∀ k,
    CMem p (binAux p zr zi u k).1
        (∑ i ∈ Finset.range k, Ring.choose (zC zr zi) i * ((u : ℝ) : ℂ) ^ i) ∧
      CMem p (binAux p zr zi u k).2 (Ring.choose (zC zr zi) k * ((u : ℝ) : ℂ) ^ k)
  | 0 => ⟨by simpa [binAux] using mem_cof p 0 0, by simpa [binAux] using mem_cof p 1 0⟩
  | k + 1 => by
    obtain ⟨hS, hT⟩ := binAux_mem zr zi u k
    rcases h : binAux p zr zi u k with ⟨S, T⟩
    rw [h] at hS hT
    simp only [binAux, h]
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_range_succ]; exact mem_cadd p hS hT
    · have := mem_csmul p (mem_ofQ p (u / (k + 1)))
        (mem_cmul p hT ((mem_cof p (zr - k) zi).congr p (cof_sub zr zi k)))
      exact this.congr p (bin_step _ u k)

/-- The moment step in the form the checker uses. -/
lemma mom_step {α : ℝ} (hα : α ≠ 0) (a h : ℚ) (k : ℕ) :
    ((((k + 1 : ℚ) : ℝ) * mom α a (a + h : ℚ) k - Real.exp (-α * ((a + h : ℚ) : ℝ)) *
        ((h ^ (k + 1) : ℚ) : ℝ)) * α⁻¹) = mom α a (a + h : ℚ) (k + 1) := by
  have e := mom_succ α a (a + h : ℚ) k
  have hb : (((a + h : ℚ) : ℝ) - (a : ℝ)) = (h : ℝ) := by push_cast; ring
  rw [hb] at e
  field_simp
  push_cast at e ⊢
  simp only [neg_mul] at e ⊢
  linear_combination -e

theorem cellAux_mem (zr zi ainv a h : ℚ) {α : ℝ} (hα : α ≠ 0) {invA Eb I0 : Iv}
    (hinv : invA.Mem p α⁻¹) (hEb : Eb.Mem p (Real.exp (-α * ((a + h : ℚ) : ℝ))))
    (hI0 : I0.Mem p (mom α a (a + h : ℚ) 0)) : ∀ k,
    CMem p (cellAux p zr zi ainv h invA Eb I0 k).1
        (∑ i ∈ Finset.range k, ((mom α a (a + h : ℚ) i : ℝ) : ℂ) *
          (Ring.choose (zC zr zi) i * ((ainv : ℝ) : ℂ) ^ i)) ∧
      CMem p (cellAux p zr zi ainv h invA Eb I0 k).2.1
        (Ring.choose (zC zr zi) k * ((ainv : ℝ) : ℂ) ^ k) ∧
      (cellAux p zr zi ainv h invA Eb I0 k).2.2.Mem p (mom α a (a + h : ℚ) k)
  | 0 => ⟨by simpa [cellAux] using mem_cof p 0 0, by simpa [cellAux] using mem_cof p 1 0,
      by simpa [cellAux] using hI0⟩
  | k + 1 => by
    obtain ⟨hS, hT, hI⟩ := cellAux_mem zr zi ainv a h hα hinv hEb hI0 k
    rcases hc : cellAux p zr zi ainv h invA Eb I0 k with ⟨S, T, J⟩
    rw [hc] at hS hT hI
    simp only [cellAux, hc]
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.sum_range_succ]; exact mem_cadd p hS (mem_csmul p hI hT)
    · have := mem_csmul p (mem_ofQ p (ainv / (k + 1)))
        (mem_cmul p hT ((mem_cof p (zr - k) zi).congr p (cof_sub zr zi k)))
      exact this.congr p (bin_step _ ainv k)
    · have := Iv.mem_mul p (mem_isub p (Iv.mem_mul p (mem_ofQ p (k + 1)) hI)
        (Iv.mem_mul p hEb (mem_ofQ p (h ^ (k + 1))))) hinv
      exact Mem.congr p this (mom_step hα a h k)

/-- `β_k` in `ℚ` is `β_k` in `ℝ`. -/
lemma betaQ_cast (M : ℚ) : ∀ k, ((betaQ M k : ℚ) : ℝ) = beta (M : ℝ) k
  | 0 => by simp [betaQ, beta]
  | k + 1 => by rw [betaQ, beta, ← betaQ_cast M k]; push_cast; ring

lemma remQ_cast (M : ℚ) (d : ℕ) (U : ℚ) :
    ((remQ M d U : ℚ) : ℝ) = beta (M : ℝ) (d + 1) * (U : ℝ) ^ (d + 1) /
      (1 - (U : ℝ) * ((M : ℝ) + d + 1) / (d + 2)) := by
  rw [remQ, ← betaQ_cast]; push_cast; ring

end AEGIS.RHCheckSoundV1

#print axioms AEGIS.RHCheckSoundV1.binAux_mem
#print axioms AEGIS.RHCheckSoundV1.cellAux_mem
