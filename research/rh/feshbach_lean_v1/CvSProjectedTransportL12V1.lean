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

import CvSFiniteCongruenceV1
import CvSProjectedSchurBridgeL12V1

/-!
# Exact transport to the existing CvS quadratic form

This is finite congruence and reindexing for the definitions in
`CvSProjectedPackedCertificateL12V1` and `CvSSchurClosureFromBoundsV1`.
It uses neither positivity, symmetry, interval enclosures, nor invertibility
of the rational change of basis. The analytic certificate premises remain
explicit in the coercivity consumer.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace AEGIS.CvSProjectedTransportL12V1

set_option maxRecDepth 4000
set_option maxHeartbeats 800000

open AEGIS.CvSFiniteCongruenceV1 AEGIS.CvSMomentBasisV1
open AEGIS.CvSLowBlockMatrixV1 AEGIS.CvSProjectedPackedCertificateL12V1
open AEGIS.CvSProjectedSchurBridgeL12V1 AEGIS.CvSSchurClosureFromBoundsV1

/-- Distinct finite indices give distinct signed frequencies. -/
theorem signedFreq_injective : Function.Injective signedFreq := by
  intro i j h
  apply Fin.ext
  simp only [signedFreq] at h
  omega

/-- The actual three-point atom supports cover exactly the signed interval. -/
theorem lowFreq_mem_iff (k : ℤ) :
    k ∈ lowFreq (fun i : Fin 139 => sinSqSupport (atomCenter i)) ↔
      -70 ≤ k ∧ k ≤ 70 := by
  constructor
  · intro hk
    simp only [lowFreq, Finset.mem_biUnion, Finset.mem_univ, true_and] at hk
    obtain ⟨i, hi⟩ := hk
    have h := i.isLt
    simp only [sinSqSupport, Finset.mem_insert, Finset.mem_singleton, atomCenter] at hi
    omega
  · rintro ⟨hlo, hhi⟩
    simp only [lowFreq, Finset.mem_biUnion, Finset.mem_univ, true_and]
    by_cases h : k = -70
    · refine ⟨⟨0, by omega⟩, ?_⟩
      simp [sinSqSupport, atomCenter, h]
    by_cases h' : k = 70
    · refine ⟨⟨138, by omega⟩, ?_⟩
      simp [sinSqSupport, atomCenter, h']
    · have hnonneg : 0 ≤ k + 69 := by omega
      refine ⟨⟨(k + 69).toNat, by omega⟩, ?_⟩
      simp only [sinSqSupport, Finset.mem_insert, Finset.mem_singleton, atomCenter]
      exact Or.inr (Or.inl (by omega))

/-- Sum over signed indices by the exact support bijection. -/
theorem sum_signedFreq {V : Type*} [AddCommMonoid V] (f : ℤ → V) :
    (∑ k : Fin 141, f (signedFreq k)) =
      ∑ k ∈ lowFreq (fun i : Fin 139 => sinSqSupport (atomCenter i)), f k := by
  apply Finset.sum_bij (fun k _ => signedFreq k)
  · intro k _
    rw [lowFreq_mem_iff]
    have h := k.isLt
    simp only [signedFreq]
    omega
  · intro i _ j _ h
    exact signedFreq_injective h
  · intro k hk
    rw [lowFreq_mem_iff] at hk
    refine ⟨⟨(k + 70).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    simp only [signedFreq]
    omega
  · intro k _
    rfl

/-- The real frequency factor is exactly the source ODE factor. -/
theorem frequency_factor (k : Fin 141) :
    ((-(2 * Real.pi * (signedFreq k : ℝ) / (6 / 5 : ℝ)) ^ 2 - 1 / 4 : ℝ) : ℂ) =
      iw (6 / 5) (signedFreq k) * iw (6 / 5) (signedFreq k) - 1 / 4 := by
  simp only [iw]
  push_cast
  ring_nf
  simp [Complex.I_sq]
  ring

/-- A stored real atom weight equals its guarded source Fourier coefficient. -/
theorem atomWeight_eq (i : Fin 139) (k : Fin 141) :
    (atomWeight i k : ℂ) =
      if signedFreq k ∈ sinSqSupport (atomCenter i) then
        sinSqWeight (atomCenter i) (signedFreq k) *
          (iw (6 / 5) (signedFreq k) * iw (6 / 5) (signedFreq k) - 1 / 4)
      else 0 := by
  rw [atomWeight, Complex.ofReal_mul, frequency_factor]
  by_cases hc : signedFreq k = atomCenter i
  · simp [sinSqSupport, sinSqWeight, hc]
  by_cases hs : signedFreq k = atomCenter i - 1 ∨ signedFreq k = atomCenter i + 1
  · have hm : signedFreq k ∈ sinSqSupport (atomCenter i) := by
      simpa only [sinSqSupport, Finset.mem_insert, Finset.mem_singleton] using
        hs.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inr h))
    simp [hc, hs, hm, sinSqWeight]
  · have hm : signedFreq k ∉ sinSqSupport (atomCenter i) := by
      simp only [sinSqSupport, Finset.mem_insert, Finset.mem_singleton]
      tauto
    simp [hc, hs, hm]

/-- The transformed coefficients represent the source low-block coefficients. -/
theorem transformed_coeff_eq_lowCoeff (v : Fin 139 → ℂ) (k : Fin 141) :
    (∑ i : Fin 139, (transformedCoeff k i : ℂ) * v i) =
      lowCoeff (6 / 5) (fun i => sinSqSupport (atomCenter i))
        (fun i => sinSqWeight (atomCenter i)) (R_basis v) (signedFreq k) := by
  simp only [transformedCoeff, Complex.ofReal_sum, Complex.ofReal_mul]
  rw [AEGIS.CvSFiniteCongruenceV1.transformed_coeff_linear
    (fun k j => (atomWeight j k : ℂ)) (fun j i => (rCoeff j i : ℂ)) v k]
  unfold lowCoeff
  apply Finset.sum_congr rfl
  intro i _
  rw [atomWeight_eq]
  simp only [R_basis]
  ring

/-- Congruence before replacing the signed finite frequency index. -/
theorem projectedQ_eq_signed_form (M : ℕ) (v : Fin 139 → ℂ) :
    projectedQ M v =
      (∑ k : Fin 141, ∑ l : Fin 141,
        lowCoeff (6 / 5) (fun i => sinSqSupport (atomCenter i))
          (fun i => sinSqWeight (atomCenter i)) (R_basis v) (signedFreq k) *
        conj (lowCoeff (6 / 5) (fun i => sinSqSupport (atomCenter i))
          (fun i => sinSqWeight (atomCenter i)) (R_basis v) (signedFreq l)) *
        (signedEntry M k l : ℂ)).re := by
  unfold projectedQ projectedEntry
  rw [quadratic_form_real_congruence (signedEntry M) transformedCoeff v]
  simp_rw [transformed_coeff_eq_lowCoeff]

/-- The exact, premise-free transport required by the existing Schur bridge. -/
theorem hTransport (M : ℕ) (v : Fin 139 → ℂ) :
    projectedQ M v = Q_CvS M (6 / 5) atomCenter (R_basis v) := by
  rw [projectedQ_eq_signed_form]
  unfold Q_CvS
  simp only [signedEntry]
  let f : ℤ → ℤ → ℂ := fun k l =>
    lowCoeff (6 / 5) (fun i => sinSqSupport (atomCenter i))
      (fun i => sinSqWeight (atomCenter i)) (R_basis v) k *
    conj (lowCoeff (6 / 5) (fun i => sinSqSupport (atomCenter i))
      (fun i => sinSqWeight (atomCenter i)) (R_basis v) l) * (A_CvS M (6 / 5) k l : ℂ)
  change (∑ k : Fin 141, ∑ l : Fin 141, f (signedFreq k) (signedFreq l)).re =
    (∑ k ∈ lowFreq (fun i : Fin 139 => sinSqSupport (atomCenter i)),
      ∑ l ∈ lowFreq (fun i : Fin 139 => sinSqSupport (atomCenter i)), f k l).re
  apply congrArg Complex.re
  calc
    _ = ∑ k ∈ lowFreq (fun i : Fin 139 => sinSqSupport (atomCenter i)),
        ∑ l : Fin 141, f k (signedFreq l) :=
      sum_signedFreq (fun k => ∑ l : Fin 141, f k (signedFreq l))
    _ = _ := Finset.sum_congr rfl fun k _ => sum_signedFreq (f k)

/-- The existing coercivity consumer with transport discharged. -/
theorem original_atom_coercivity_of_transport (M : ℕ) (kappa : ℝ) (hkappa : 0 < kappa)
    (hIv : ∀ i j : Fin 139,
      (AEGIS.CvSPackedGramV1.Im certI i.val j.val).Mem certQ (projectedEntry M i j))
    (hRsurj : Function.Surjective R_basis)
    (hRnorm : ∀ v, normSqCoeffs (R_basis v) ≤ kappa * normSqCoeffs v) :
    ∀ c, (certifiedMu / kappa) * normSqCoeffs c ≤
      Q_CvS M (6 / 5) atomCenter c := by
  exact AEGIS.CvSProjectedSchurBridgeL12V1.original_atom_coercivity
    M kappa hkappa hIv hRsurj hRnorm (hTransport M)

/-- The existing low-block Schur consumer with transport discharged. -/
theorem hlow_of_projected_packed_of_transport (M : ℕ)
    (m T_trace beta kappa : ℝ)
    (Brow : (Fin 139 → ℂ) → ℝ)
    (hkappa : 0 < kappa)
    (hgap : 0 < m - T_trace / (2 * Real.pi))
    (hIv : ∀ i j : Fin 139,
      (AEGIS.CvSPackedGramV1.Im certI i.val j.val).Mem certQ (projectedEntry M i j))
    (hRsurj : Function.Surjective R_basis)
    (hRnorm : ∀ v, normSqCoeffs (R_basis v) ≤ kappa * normSqCoeffs v)
    (hBrow : ∀ c, Brow c ≤ beta * normSqCoeffs c)
    (hbeta : beta ≤ (2 * Real.pi) ^ 2 * (6 / 5 : ℝ) *
        (m - T_trace / (2 * Real.pi)) * (certifiedMu / kappa)) :
    ∀ c, Brow c / (2 * Real.pi * (6 / 5 : ℝ)) /
      (m - T_trace / (2 * Real.pi)) ≤
      2 * Real.pi * Q_CvS M (6 / 5) atomCenter c := by
  exact AEGIS.CvSProjectedSchurBridgeL12V1.hlow_of_projected_packed
    M m T_trace beta kappa Brow hkappa hgap hIv hRsurj hRnorm (hTransport M) hBrow hbeta

end AEGIS.CvSProjectedTransportL12V1

#print axioms AEGIS.CvSProjectedTransportL12V1.signedFreq_injective
#print axioms AEGIS.CvSProjectedTransportL12V1.lowFreq_mem_iff
#print axioms AEGIS.CvSProjectedTransportL12V1.sum_signedFreq
#print axioms AEGIS.CvSProjectedTransportL12V1.frequency_factor
#print axioms AEGIS.CvSProjectedTransportL12V1.atomWeight_eq
#print axioms AEGIS.CvSProjectedTransportL12V1.transformed_coeff_eq_lowCoeff
#print axioms AEGIS.CvSProjectedTransportL12V1.projectedQ_eq_signed_form
#print axioms AEGIS.CvSProjectedTransportL12V1.hTransport

#print axioms AEGIS.CvSProjectedTransportL12V1.original_atom_coercivity_of_transport
#print axioms AEGIS.CvSProjectedTransportL12V1.hlow_of_projected_packed_of_transport
