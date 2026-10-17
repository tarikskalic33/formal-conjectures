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

import Mathlib

/-!
# AEGIS Ω V7 — exact rational audit of a proposed zeta-to-V6 proxy

The arithmetic is formally verified. Bounds on true Riemann zeta zeros
and a physical gamma-to-Weil-to-gravity map are NOT asserted here.
No additional axioms, RH premise, or sorry.
-/

namespace AEGIS.H64ZetaMappingAuditV1

/-- The trace of the Gram of the unnormalized 64-state Walsh matrix is
64×64 when H²=64I. This theorem certifies only that integer arithmetic. -/
theorem h64_frobenius_trace_count : (64 : ℕ) * 64 = 4096 := by
  norm_num

/-- The proposed trace fourth root 8 is exact and dimensionless. -/
theorem h64_trace_fourth_root_arithmetic : (8 : ℕ) ^ 4 = 4096 := by
  norm_num

/-- Exact inverse coefficient in Q16.16. -/
theorem h64_inverse_q16 : (1024 : ℕ) * 64 = 65536 := by
  norm_num

/-- If one ordinate is >=14 and seven are >=21, their reciprocal-square-root
sum divided by 64 is bounded above by this exact rational expression. -/
theorem eight_ordinate_coarse_bound :
    ((2 / 7 : ℚ) + 7 * (2 / 9 : ℚ)) / 64 = (29 / 1008 : ℚ) := by
  norm_num

/-- The rational ceiling is strictly below the V6 shooting seed 0.03. -/
theorem bound_strictly_below_v6_seed :
    (29 / 1008 : ℚ) < (3 / 100 : ℚ) := by
  norm_num

/-- Conditional separation, requiring an explicit, externally established
proxy bound. It is not inferred from an unproved zeta-to-Weil mapping. -/
theorem bounded_proxy_cannot_equal_v6_seed (proxy : ℝ)
    (hproxy : proxy ≤ (29 / 1008 : ℝ)) :
    proxy ≠ (3 / 100 : ℝ) := by
  intro heq
  rw [heq] at hproxy
  norm_num at hproxy


/-! ## V8 Rayleigh witness: exact algebra and π inequality

These theorems formalize the strictly negative arithmetic Rayleigh
expression. The improper integral evaluations producing the kinetic and
curvature coefficients were checked independently with SymPy/mpmath;
they are not Lean theorems in this source. Nothing here infers physical
couplings from zeta ordinates, nor asserts an RH theorem.
-/

/-- Rationally certified Archimedean ceiling on π from Mathlib. -/
theorem pi_lt_classical_twenty_two_sevenths :
    Real.pi < (22 / 7 : ℝ) := by
  have h := Real.pi_lt_d4
  linarith

/-- The exactly simplified quadratic form at λ=1/2 (ξ=8π). -/
theorem rayleigh_trial_half_coupling_algebra :
    (Real.pi / 8 - (8 / 63 : ℝ)) -
      (1 / 2 : ℝ) * (8 / 15 : ℝ) =
        Real.pi / 8 - (124 / 315 : ℝ) := by
  ring

/-- The V8 witness is strictly negative without floating-point input. -/
theorem rayleigh_trial_strictly_negative :
    Real.pi / 8 - (124 / 315 : ℝ) <
      -(1 / 1260 : ℝ) := by
  have hpi := pi_lt_classical_twenty_two_sevenths
  linarith

/-- Exact algebra of the one-mode Rayleigh quotient, provided separately
verified analytic kinetic and curvature integrals are used. -/
theorem rayleigh_trial_quotient_algebra :
    (Real.pi / 8 - (8 / 63 : ℝ)) / (8 / 15 : ℝ) =
      15 * Real.pi / 64 - (5 / 21 : ℝ) := by
  ring

/-- The named integral values imply the negative quadratic form.
No claim is made that Lean has proved those improper integrals. -/
theorem rayleigh_negative_of_integral_values
    (kinetic curvature : ℝ)
    (hk : kinetic = Real.pi / 8 - (8 / 63 : ℝ))
    (hR : curvature = (8 / 15 : ℝ)) :
    kinetic - (1 / 2 : ℝ) * curvature < 0 := by
  calc
    kinetic - (1 / 2 : ℝ) * curvature =
        Real.pi / 8 - (124 / 315 : ℝ) := by
          rw [hk, hR]
          exact rayleigh_trial_half_coupling_algebra
    _ < -(1 / 1260 : ℝ) := rayleigh_trial_strictly_negative
    _ < 0 := by norm_num

/-- The rationally chosen second trial mode preserves the exact kinetic
numerator; this is symbolic coefficient algebra, NOT a Lean integral. -/
theorem rayleigh_two_mode_kinetic_algebra :
    (Real.pi / 8 - (8 / 63 : ℝ)) -
      (2 / 25 : ℝ) * (3 * Real.pi / 32 - (64 / 693 : ℝ)) +
      (1 / 625 : ℝ) * (3 * Real.pi / 32 - (256 / 3003 : ℝ)) =
        2353 * Real.pi / 20000 - (61288 / 511875 : ℝ) := by
  ring

/-- The two-mode curvature denominator is rational and strictly positive. -/
theorem rayleigh_two_mode_curvature_algebra :
    (8 / 15 : ℝ) - (2 / 25 : ℝ) * (464 / 1155 : ℝ) +
      (1 / 625 : ℝ) * (4736 / 15015 : ℝ) =
        (4708136 / 9384375 : ℝ) := by
  norm_num

theorem rayleigh_two_mode_curvature_positive :
    (0 : ℝ) < 4708136 / 9384375 := by norm_num

end AEGIS.H64ZetaMappingAuditV1

#print axioms AEGIS.H64ZetaMappingAuditV1.h64_frobenius_trace_count
#print axioms AEGIS.H64ZetaMappingAuditV1.h64_trace_fourth_root_arithmetic
#print axioms AEGIS.H64ZetaMappingAuditV1.h64_inverse_q16
#print axioms AEGIS.H64ZetaMappingAuditV1.eight_ordinate_coarse_bound
#print axioms AEGIS.H64ZetaMappingAuditV1.bound_strictly_below_v6_seed
#print axioms AEGIS.H64ZetaMappingAuditV1.bounded_proxy_cannot_equal_v6_seed

#print axioms AEGIS.H64ZetaMappingAuditV1.pi_lt_classical_twenty_two_sevenths
#print axioms AEGIS.H64ZetaMappingAuditV1.rayleigh_trial_half_coupling_algebra
#print axioms AEGIS.H64ZetaMappingAuditV1.rayleigh_trial_strictly_negative
#print axioms AEGIS.H64ZetaMappingAuditV1.rayleigh_trial_quotient_algebra
#print axioms AEGIS.H64ZetaMappingAuditV1.rayleigh_negative_of_integral_values
#print axioms AEGIS.H64ZetaMappingAuditV1.rayleigh_two_mode_kinetic_algebra
#print axioms AEGIS.H64ZetaMappingAuditV1.rayleigh_two_mode_curvature_algebra
#print axioms AEGIS.H64ZetaMappingAuditV1.rayleigh_two_mode_curvature_positive
