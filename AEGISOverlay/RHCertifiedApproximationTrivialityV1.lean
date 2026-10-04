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

import RHCertifiedApproximationV1

/-!
# The scalar approximation obligation is equivalent to its target

`DyadicArithmeticApproximationV1` asks only that the *values*
`arithmeticValue (p n)` converge to `arithmeticValue g`; it does not ask that
`p n` approach `g`.  Certified tower packets are closed under real rescaling of
their coefficient vector, and the form is quadratic, so one certified packet
with a negative value reaches every nonpositive real exactly.  Hence, given such
a witness, the obligation is equivalent to nonpositivity of `arithmeticValue`
on every moment-zero packet, which is the restricted Weil target itself.

A non-circular globalization step must therefore approximate `g` itself in a
topology in which the actual Weil form is continuous.
-/

open Filter Topology Complex
open scoped BigOperators ComplexConjugate

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHCertifiedApproximationTrivialityV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.RHGramExpansionV13
open AEGIS.RHDyadicTowerV13
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHMillenniumGateV10
open AEGIS.RHCertifiedApproximationV1

/-- Rescaling the tower coefficients by a real `t` multiplies the value by `t ^ 2`. -/
theorem arithmeticValue_tower_smul (N : ℕ) (g : WeilCompactSmoothGV1)
    (z : Fin (N + 1) → ℂ) (t : ℝ) :
    arithmeticValue (towerPacket N g (fun i => (t : ℂ) * z i)) =
      t ^ 2 * arithmeticValue (towerPacket N g z) := by
  unfold arithmeticValue
  change (B (towerPacket N g (fun i => (t : ℂ) * z i))
      (towerPacket N g (fun i => (t : ℂ) * z i))).re =
    t ^ 2 * (B (towerPacket N g z) (towerPacket N g z)).re
  unfold towerPacket
  rw [B_packetSum, B_packetSum]
  have hterm : ∀ i j : Fin (N + 1),
      (t : ℂ) * z i * star ((t : ℂ) * z j) * B (translates N g i) (translates N g j) =
        ((t ^ 2 : ℝ) : ℂ) * (z i * star (z j) * B (translates N g i) (translates N g j)) := by
    intro i j
    rw [star_mul', Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  simp_rw [hterm, ← Finset.mul_sum]
  rw [Complex.re_ofReal_mul]

/-- One certified packet with a negative value reaches every nonpositive value exactly. -/
theorem approximation_of_arithmetic_nonpositive
    (p0 : WeilCompactSmoothGV1) (hp0 : DyadicCertified p0) (hneg : arithmeticValue p0 < 0)
    (hall : ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g → arithmeticValue g ≤ 0) :
    DyadicArithmeticApproximationV1 := by
  intro g hm
  obtain ⟨N, m, g0, a, z, hm10, hmN, hwg, hmom, rfl⟩ := hp0
  set w := arithmeticValue (towerPacket N g0 z) with hw
  have hv : arithmeticValue g ≤ 0 := hall g hm
  set t : ℝ := Real.sqrt (arithmeticValue g / w)
  have hval : arithmeticValue (towerPacket N g0 (fun i => (t : ℂ) * z i)) =
      arithmeticValue g := by
    rw [arithmeticValue_tower_smul, ← hw,
      Real.sq_sqrt (div_nonneg_of_nonpos hv hneg.le)]
    field_simp [hneg.ne]
  refine ⟨fun _ => towerPacket N g0 (fun i => (t : ℂ) * z i),
    fun _ => ⟨N, m, g0, a, _, hm10, hmN, hwg, hmom, rfl⟩, ?_⟩
  simp only [hval]
  exact tendsto_const_nhds

/-- Given one strictly negative certificate, the approximation obligation is
equivalent to nonpositivity of the arithmetic form on every moment-zero packet. -/
theorem approximation_iff_arithmetic_nonpositive
    (hwit : ∃ p, DyadicCertified p ∧ arithmeticValue p < 0) :
    DyadicArithmeticApproximationV1 ↔
      ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g → arithmeticValue g ≤ 0 := by
  constructor
  · intro happrox g hm
    obtain ⟨p, hp, hlim⟩ := happrox g hm
    exact arithmetic_nonpositive_of_certified_limit DyadicCertified
      dyadicCertified_nonpositive g p hp hlim
  · intro hall
    obtain ⟨p0, hp0, hneg⟩ := hwit
    exact approximation_of_arithmetic_nonpositive p0 hp0 hneg hall

/-- The same equivalence stated against the repository's zero-side target. -/
theorem approximation_iff_universal
    (hwit : ∃ p, DyadicCertified p ∧ arithmeticValue p < 0) :
    DyadicArithmeticApproximationV1 ↔ UniversalZeroQuadraticNonnegativeV10 := by
  rw [approximation_iff_arithmetic_nonpositive hwit]
  constructor
  · intro hall g hm
    exact (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 g hm).mp (hall g hm)
  · intro huniv g hm
    exact (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 g hm).mpr (huniv g hm)

#print axioms AEGIS.RHCertifiedApproximationTrivialityV1.arithmeticValue_tower_smul
#print axioms AEGIS.RHCertifiedApproximationTrivialityV1.approximation_iff_arithmetic_nonpositive
#print axioms AEGIS.RHCertifiedApproximationTrivialityV1.approximation_iff_universal

end AEGIS.RHCertifiedApproximationTrivialityV1
