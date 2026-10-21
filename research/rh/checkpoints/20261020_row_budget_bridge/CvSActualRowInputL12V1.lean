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
/- Source memberships for the fixed L=6/5 relative row-budget calculation.
No output-table or positivity assumption is discharged by this input layer. -/
import CvSProjectedEntryL12V1
import CvSGramTailV1
import CvSTauSigned150L12V1
import CvSFrequencyIntervalV1
import CvSIntervalDivideV1
import CvSActualCrossRowL12V1
import CvSIntervalMatrixProductV1

open scoped BigOperators

namespace AEGIS.CvSActualRowInputL12V1
open AEGIS.RHFixIntervalV1 AEGIS.CvSRationalIntervalV1
open AEGIS.CvSProjectedPackedCertificateL12V1 AEGIS.CvSProjectedEntryL12V1

/-- The actual transformed source coefficient, enclosed at arbitrary precision. -/
theorem transformedCoeff_mem (p : ℕ) (k : Fin 141) (i : Fin 139) :
    (AEGIS.CvSFrequencyIntervalV1.coefficientInterval p (signedFreq k)
      (wZ (signedFreq k) i)).Mem p (transformedCoeff k i) := by
  rw [transformedCoeff_eq]
  exact AEGIS.CvSFrequencyIntervalV1.coefficient_mem p (signedFreq k) (wZ (signedFreq k) i)

/-- Exact rational harmonic Gram kernel; the diagonal is the source upper bound. -/
def gramRat (NP : ℕ) (n m : ℤ) : ℚ :=
  if n = m then 1 / ((NP : ℚ) - n + 1 / 2) + 1 / ((NP : ℚ) + n + 1 / 2)
  else (harmonic ((NP : ℤ) - m).toNat - harmonic ((NP : ℤ) - n).toNat +
    (harmonic ((NP : ℤ) + n).toNat - harmonic ((NP : ℤ) + m).toNat)) / ((n : ℚ) - m)

/-- Identifies the rational data with the original real source definition. -/
theorem gramRat_cast (NP : ℕ) (n m : ℤ) :
    (gramRat NP n m : ℝ) = AEGIS.CvSGramTailV1.gramUp NP n m := by
  simp only [gramRat, AEGIS.CvSGramTailV1.gramUp, AEGIS.CvSGramTailV1.H]
  split_ifs <;> push_cast <;> rfl

/-- No numerical harmonic approximation is used. -/
theorem gramUp_mem (p NP : ℕ) (n m : ℤ) :
    (rationalRange p (gramRat NP n m) (gramRat NP n m)).Mem p
      (AEGIS.CvSGramTailV1.gramUp NP n m) := by
  rw [← gramRat_cast]
  exact rationalRange_mem p _ _ le_rfl le_rfl

/-- The exact source Gram kernel is symmetric at every cutoff. -/
theorem gramUp_symm (NP : ℕ) (n m : ℤ) :
    AEGIS.CvSGramTailV1.gramUp NP n m = AEGIS.CvSGramTailV1.gramUp NP m n := by
  by_cases h : n = m
  · subst m
    rfl
  · simp only [AEGIS.CvSGramTailV1.gramUp, if_neg h, if_neg (Ne.symm h)]
    rw [show (m : ℝ) - n = -((n : ℝ) - m) by ring, div_neg, ← neg_div]
    congr 1
    ring

def diagonalBox (p : ℕ) (n : ℤ) : Iv :=
  rationalRange p (AEGIS.CvSDiagL12V1.diagLo.getD n.natAbs 0)
    (AEGIS.CvSDiagL12V1.diagHi.getD n.natAbs 0)

/-- Existing positive diagonal boxes transported to both signed frequencies. -/
theorem diagonal_mem (p : ℕ) {M : ℕ} (hM : 3 ≤ M) (n : ℤ) (hn : n.natAbs ≤ 70) :
    (diagonalBox p n).Mem p (AEGIS.CvSLowBlockMatrixV1.cvsEntry M (6 / 5) n n) := by
  set a := n.natAbs with ha
  have hcv : AEGIS.CvSLowBlockMatrixV1.cvsEntry M (6 / 5) n n =
      AEGIS.CvSLowBlockMatrixV1.cvsEntry M (6 / 5) (a : ℤ) (a : ℤ) := by
    rcases Int.natAbs_eq n with h | h
    · rw [← ha] at h
      rw [h]
    · rw [← ha] at h
      rw [h, AEGIS.CvSDiagL12V1.cvsEntry_diag_neg hM]
  rw [hcv]
  exact rationalRange_mem p _ _ (AEGIS.CvSDiagL12V1.diag_mem hM hn).1
    (AEGIS.CvSDiagL12V1.diag_mem hM hn).2

def tauBox (p : ℕ) (n : ℤ) : Iv := rationalRange p
  (AEGIS.CvSTauSigned150L12V1.signedLo n) (AEGIS.CvSTauSigned150L12V1.signedHi n)

/-- Same diagonal doubling, signed difference and integer division as the generator. -/
def kernelBox (p : ℕ) (m : ℤ) (k : Fin 141) : Iv :=
  if m = signedFreq k then
    ((rationalRange p AEGIS.CvSFrequencyIntervalV1.piLo AEGIS.CvSFrequencyIntervalV1.piHi).add
      (rationalRange p AEGIS.CvSFrequencyIntervalV1.piLo AEGIS.CvSFrequencyIntervalV1.piHi)).mul p
        (diagonalBox p (signedFreq k))
  else (AEGIS.CvSFrequencyIntervalV1.lpInterval p).mul p
    (AEGIS.CvSIntervalDivideV1.divInt ((tauBox p (signedFreq k)).add (tauBox p m).neg)
      (signedFreq k - m))

/-- The actual CvS cross kernel is enclosed, including the signed diagonal branch. -/
theorem sourceKernel_mem (p : ℕ) {M : ℕ} (hM : 3 ≤ M) (m : ℤ)
    (hm : m.natAbs ≤ 150) (k : Fin 141) :
    (kernelBox p m k).Mem p (AEGIS.CvSActualCrossRowL12V1.sourceKernel M m (signedFreq k)) := by
  have hn : (signedFreq k).natAbs ≤ 70 := by
    have hk := k.isLt
    simp only [signedFreq]
    omega
  by_cases h : m = signedFreq k
  · rw [kernelBox, if_pos h, h, AEGIS.CvSActualCrossRowL12V1.sourceKernel_diag]
    have hpi := rationalRange_mem p _ _ AEGIS.CvSFrequencyIntervalV1.pi_bounds.1
      AEGIS.CvSFrequencyIntervalV1.pi_bounds.2
    simpa only [two_mul] using Iv.mem_mul p (Iv.mem_add p hpi hpi)
      (diagonal_mem p hM (signedFreq k) hn)
  · rw [kernelBox, if_neg h, AEGIS.CvSActualCrossRowL12V1.sourceKernel_off M m (signedFreq k) (Ne.symm h)]
    have ht := Iv.mem_add p
      (AEGIS.CvSTauSigned150L12V1.signed_tau_interval p hM (signedFreq k) (by omega))
      (Iv.mem_neg p (AEGIS.CvSTauSigned150L12V1.signed_tau_interval p hM m hm))
    have hdiv := AEGIS.CvSIntervalDivideV1.divInt_mem p ht (sub_ne_zero.mpr (Ne.symm h))
    simpa only [tauBox, sub_eq_add_neg, Int.cast_add, Int.cast_neg, Int.cast_sub] using
      Iv.mem_mul p (AEGIS.CvSFrequencyIntervalV1.lp_mem p) hdiv

def sourceYBox (p : ℕ) (m : ℤ) (i : Fin 139) : Iv :=
  AEGIS.CvSIntervalMatrixProductV1.dot p (kernelBox p m)
    (fun k => AEGIS.CvSFrequencyIntervalV1.coefficientInterval p (signedFreq k) (wZ (signedFreq k) i))

/-- Input enclosure for every genuine finite cross row; no positivity premise. -/
theorem sourceY_mem (p : ℕ) {M : ℕ} (hM : 3 ≤ M) (m : ℤ)
    (hm : m.natAbs ≤ 150) (i : Fin 139) :
    (sourceYBox p m i).Mem p (AEGIS.CvSActualCrossRowL12V1.sourceY M m i) := by
  have h := AEGIS.CvSIntervalMatrixProductV1.dot_mem p (kernelBox p m)
    (fun k => AEGIS.CvSFrequencyIntervalV1.coefficientInterval p (signedFreq k) (wZ (signedFreq k) i))
    (fun k => AEGIS.CvSActualCrossRowL12V1.sourceKernel M m (signedFreq k))
    (fun k => transformedCoeff k i) (sourceKernel_mem p hM m hm)
    (fun k => transformedCoeff_mem p k i)
  have heq : (∑ k : Fin 141,
      AEGIS.CvSActualCrossRowL12V1.sourceKernel M m (signedFreq k) * transformedCoeff k i) =
      AEGIS.CvSActualCrossRowL12V1.sourceY M m i := by
    unfold AEGIS.CvSActualCrossRowL12V1.sourceY
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  rw [heq] at h
  exact h


/-- The generator indexes 301 actual cross rows by m = -150,...,150. -/
def rowIndex (r : Fin 301) : ℤ := (r.val : ℤ) - 150

/-- The existing actual transformed source coefficient at Q96. -/
def xBox (k : Fin 141) (i : Fin 139) : Iv :=
  AEGIS.CvSFrequencyIntervalV1.coefficientInterval 96
    (signedFreq k) (wZ (signedFreq k) i)

/-- The actual residual Y - X*Lambda, with the subtraction restricted to
the 141 inner source rows. Lambda is an arbitrary real projection. -/
noncomputable def sourceZ (M : ℕ) (lam : Fin 139 → Fin 139 → ℝ)
    (r : Fin 301) (i : Fin 139) : ℝ :=
  if hr : 80 ≤ r.val ∧ r.val < 221 then
    AEGIS.CvSActualCrossRowL12V1.sourceY M (rowIndex r) i -
      ∑ j : Fin 139,
        transformedCoeff (⟨r.val - 80, by omega⟩ : Fin 141) j * lam j i
  else AEGIS.CvSActualCrossRowL12V1.sourceY M (rowIndex r) i

/-- Exactly the existing outward Q96 residual formula, with no altered
endpoints, rounding, or choice of numerical projection. -/
def zBox (Lam : Fin 139 → Fin 139 → Iv)
    (r : Fin 301) (i : Fin 139) : Iv :=
  if hr : 80 ≤ r.val ∧ r.val < 221 then
    (sourceYBox 96 (rowIndex r) i).add
      (AEGIS.CvSIntervalMatrixProductV1.dot 96
        (xBox (⟨r.val - 80, by omega⟩ : Fin 141))
        (fun j => Lam j i)).neg
  else sourceYBox 96 (rowIndex r) i

/-- The 301x139 residual input is enclosed for every real projection whose
entries are enclosed at Q96. This does not assume Q80 tableCheck or positivity. -/
theorem sourceZ_mem (M : ℕ) (hM : 3 ≤ M)
    (lam : Fin 139 → Fin 139 → ℝ)
    (Lam : Fin 139 → Fin 139 → Iv)
    (hLam : ∀ j i, (Lam j i).Mem 96 (lam j i)) :
    ∀ r i, (zBox Lam r i).Mem 96 (sourceZ M lam r i) := by
  intro r i
  have hm : (rowIndex r).natAbs ≤ 150 := by
    unfold rowIndex
    have hr := r.isLt
    omega
  have hy := sourceY_mem 96 hM (rowIndex r) hm i
  by_cases hr : 80 ≤ r.val ∧ r.val < 221
  · have hx : ∀ j : Fin 139,
        (xBox (⟨r.val - 80, by omega⟩ : Fin 141) j).Mem 96
          (transformedCoeff (⟨r.val - 80, by omega⟩ : Fin 141) j) := by
      intro j
      simpa only [xBox] using
        (transformedCoeff_mem 96 (⟨r.val - 80, by omega⟩ : Fin 141) j)
    have hdot := AEGIS.CvSIntervalMatrixProductV1.dot_mem 96
      (xBox (⟨r.val - 80, by omega⟩ : Fin 141)) (fun j => Lam j i)
      (fun j => transformedCoeff (⟨r.val - 80, by omega⟩ : Fin 141) j)
      (fun j => lam j i) hx (fun j => hLam j i)
    have hres := Iv.mem_add 96 hy (Iv.mem_neg 96 hdot)
    simpa only [zBox, sourceZ, dif_pos hr, sub_eq_add_neg] using hres
  · simpa only [zBox, sourceZ, dif_neg hr] using hy


end AEGIS.CvSActualRowInputL12V1
#print axioms AEGIS.CvSActualRowInputL12V1.transformedCoeff_mem
#print axioms AEGIS.CvSActualRowInputL12V1.gramRat_cast
#print axioms AEGIS.CvSActualRowInputL12V1.gramUp_mem
#print axioms AEGIS.CvSActualRowInputL12V1.gramUp_symm
#check @AEGIS.CvSActualRowInputL12V1.transformedCoeff_mem
#check @AEGIS.CvSActualRowInputL12V1.gramRat_cast
#check @AEGIS.CvSActualRowInputL12V1.gramUp_mem
#check @AEGIS.CvSActualRowInputL12V1.gramUp_symm
#print axioms AEGIS.CvSActualRowInputL12V1.diagonal_mem
#check @AEGIS.CvSActualRowInputL12V1.diagonal_mem
#print axioms AEGIS.CvSActualRowInputL12V1.sourceKernel_mem
#check @AEGIS.CvSActualRowInputL12V1.sourceKernel_mem
#print axioms AEGIS.CvSActualRowInputL12V1.sourceY_mem
#print axioms AEGIS.CvSActualRowInputL12V1.sourceZ_mem
#check @AEGIS.CvSActualRowInputL12V1.sourceY_mem
