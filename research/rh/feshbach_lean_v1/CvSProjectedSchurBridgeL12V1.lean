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
/-
AEGIS Omega - proposed source-level bridge, read-only.
Pinned source: tarikskalic33/formal-conjectures cf9372f13370596d51eb36134f141f199ba60b5c.
Not yet compiled in Lean. This theorem accepts explicit proof obligations;
it does not elevate external numeric checks into kernel evidence.
-/
import CvSProjectedPackedCertificateL12V1
import CvSProjectedSymmetryV1
import CvSSchurClosureFromBoundsV1

open Finset Complex

namespace AEGIS.CvSProjectedSchurBridgeL12V1

open AEGIS.CvSProjectedPackedCertificateL12V1
open AEGIS.CvSPackedGramV1
open AEGIS.CvSProjectedSymmetryV1
open AEGIS.CvSSchurClosureFromBoundsV1
open AEGIS.CvSLowBlockMatrixV1
open AEGIS.CvSMomentBasisV1

/-- Change of basis as supplied by the explicit integer `certR` table. -/
noncomputable def R_basis (v : Fin 139 → ℂ) : Fin 139 → ℂ :=
  fun i => ∑ j : Fin 139, (rCoeff i j : ℂ) * v j

/-- The quadratic form in transformed coordinates. -/
noncomputable def projectedQ (M : ℕ) (v : Fin 139 → ℂ) : ℝ :=
  (∑ i : Fin 139, ∑ j : Fin 139,
    v i * (starRingEnd ℂ) (v j) * (projectedEntry M i j : ℂ)).re

/-- The rational packed margin in the actual projected coordinates. -/
noncomputable def certifiedMu : ℝ :=
  ((certEps - certEta : ℤ) : ℝ) / 2 ^ certQ

/-- A *conditional* source-to-source coercivity bridge.
The hypotheses to discharge from source are explicitly hIv,
R_basis surjectivity, a bound on R_basis, and equality of the two actual
quadratic forms. All numerical factors remain connected to the generated
packed integer certificate through `projected_lower`. -/
theorem original_atom_coercivity (M : ℕ) (kappa : ℝ) (hkappa : 0 < kappa)
    (hIv : ∀ i j : Fin 139,
      (Im certI i.val j.val).Mem certQ (projectedEntry M i j))
    (hRsurj : Function.Surjective R_basis)
    (hRnorm : ∀ v, normSqCoeffs (R_basis v) ≤ kappa * normSqCoeffs v)
    (hTransport : ∀ v,
      projectedQ M v = Q_CvS M (6 / 5) atomCenter (R_basis v)) :
    ∀ c, (certifiedMu / kappa) * normSqCoeffs c ≤
      Q_CvS M (6 / 5) atomCenter c := by
  have hmuNonneg : 0 ≤ certifiedMu := by
    unfold certifiedMu
    have hpos : (0 : ℝ) ≤ ((certEps - certEta : ℤ) : ℝ) := by
      exact_mod_cast cert_margin_positive.le
    exact div_nonneg hpos (by positivity)
  intro c
  obtain ⟨v, rfl⟩ := hRsurj c
  have hratio : normSqCoeffs (R_basis v) / kappa ≤ normSqCoeffs v :=
    (div_le_iff₀ hkappa).2 (by simpa only [mul_comm] using hRnorm v)
  have hpacked := projected_lower_of_Iv (M := M) hIv v
  have htwo : (0 : ℝ) < 2 ^ certQ := by positivity
  have hprojected : certifiedMu * normSqCoeffs v ≤ projectedQ M v := by
    have hscaled :
        ((certEps - certEta : ℤ) : ℝ) * normSqCoeffs v /
          2 ^ certQ ≤ projectedQ M v := by
      apply (div_le_iff₀ htwo).2
      simpa [normSqCoeffs, projectedQ, mul_comm] using hpacked
    calc
      certifiedMu * normSqCoeffs v =
          ((certEps - certEta : ℤ) : ℝ) * normSqCoeffs v / 2 ^ certQ := by
            unfold certifiedMu
            ring
      _ ≤ projectedQ M v := hscaled
  calc
    (certifiedMu / kappa) * normSqCoeffs (R_basis v) =
        certifiedMu * (normSqCoeffs (R_basis v) / kappa) := by ring
    _ ≤ certifiedMu * normSqCoeffs v :=
      mul_le_mul_of_nonneg_left hratio hmuNonneg
    _ ≤ projectedQ M v := hprojected
    _ = Q_CvS M (6 / 5) atomCenter (R_basis v) := hTransport v

/-- The actual CvS `hlow` for the fixed signed 139-atom family.
The remaining analytic upper budget and scalar gap are visible premises. -/
theorem hlow_of_projected_packed (M : ℕ)
    (m T_trace beta kappa : ℝ)
    (Brow : (Fin 139 → ℂ) → ℝ)
    (hkappa : 0 < kappa)
    (hgap : 0 < m - T_trace / (2 * Real.pi))
    (hIv : ∀ i j : Fin 139,
      (Im certI i.val j.val).Mem certQ (projectedEntry M i j))
    (hRsurj : Function.Surjective R_basis)
    (hRnorm : ∀ v, normSqCoeffs (R_basis v) ≤ kappa * normSqCoeffs v)
    (hTransport : ∀ v,
      projectedQ M v = Q_CvS M (6 / 5) atomCenter (R_basis v))
    (hBrow : ∀ c, Brow c ≤ beta * normSqCoeffs c)
    (hbeta : beta ≤ (2 * Real.pi) ^ 2 * (6 / 5 : ℝ) *
        (m - T_trace / (2 * Real.pi)) * (certifiedMu / kappa)) :
    ∀ c, Brow c / (2 * Real.pi * (6 / 5 : ℝ)) /
      (m - T_trace / (2 * Real.pi)) ≤
      2 * Real.pi * Q_CvS M (6 / 5) atomCenter c := by
  exact hlow_of_coercivity_and_budget (6 / 5 : ℝ) m T_trace
    (certifiedMu / kappa) beta (Q_CvS M (6 / 5) atomCenter) Brow
    (by norm_num) hgap
    (original_atom_coercivity M kappa hkappa hIv hRsurj hRnorm hTransport)
    hBrow hbeta

end AEGIS.CvSProjectedSchurBridgeL12V1

#print axioms AEGIS.CvSProjectedSchurBridgeL12V1.original_atom_coercivity
#print axioms AEGIS.CvSProjectedSchurBridgeL12V1.hlow_of_projected_packed
