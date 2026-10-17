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

import AEGISOverlay.RHMultiGeneratorComplementarityV1
import Mathlib

/-!
# Compact-window Snowflake spectral frame

The previous RHMultiGeneratorComplementarityV1 source is byte-for-byte
immutable for the historical SHA-locked Krein / consolidated proofs.
This separate module uses its proven no-common-real-zero statement to
obtain a positive frame floor on each COMPACT frequency window.

It does not assert a frequency-independent global constant, that the
spline symbols are smooth moment-zero Weil packets, or that the
arithmetic Weil quadratic form has universal sign.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHSnowflakeCompactFrameV1

open AEGIS.RHMultiGeneratorComplementarityV1

/-- On each fixed compact frequency interval, the log2/log3 moment
spline symbols have a joint positive lower bound. The constant is
window-dependent. -/
theorem log23_finite_window_uniform_gap
    {order : ℕ} (horder : order ≠ 0)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, |t| ≤ R →
        δ ≤ momentSplineSymbol order (Real.log 2) t ^ 2 +
          momentSplineSymbol order (Real.log 3) t ^ 2 := by
  let f : ℝ → ℝ := fun t =>
    momentSplineSymbol order (Real.log 2) t ^ 2 +
      momentSplineSymbol order (Real.log 3) t ^ 2
  have hf : Continuous f :=
    ((continuous_momentSplineSymbol order (Real.log 2)).pow 2).add
      ((continuous_momentSplineSymbol order (Real.log 3)).pow 2)
  have hs : IsCompact (Set.Icc (-R) R) := isCompact_Icc
  have hn : (Set.Icc (-R) R).Nonempty :=
    ⟨0, ⟨by linarith, hR⟩⟩
  obtain ⟨t, ht, hmin⟩ := hs.exists_isMinOn hn hf.continuousOn
  refine ⟨f t, ?_, ?_⟩
  · exact log23_spectral_denominator_pos horder t
  · intro u hu
    exact hmin (abs_le.mp hu)

/-- Specialization to the existing 19-point Snowflake construction. -/
theorem order19_log23_finite_window_uniform_gap
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, |t| ≤ R →
        δ ≤ momentSplineSymbol 19 (Real.log 2) t ^ 2 +
          momentSplineSymbol 19 (Real.log 3) t ^ 2 :=
  log23_finite_window_uniform_gap (by norm_num) R hR

/-- The exact simultaneous two-generator frame estimate on each
fixed finite frequency window. No uniform-in-R estimate is inferred. -/
theorem order19_log23_finite_window_frame_bound
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t u : ℝ, |t| ≤ R →
      δ * u ^ 2 ≤
        (momentSplineSymbol 19 (Real.log 2) t * u) ^ 2 +
        (momentSplineSymbol 19 (Real.log 3) t * u) ^ 2 := by
  obtain ⟨δ, hδ, hgap⟩ :=
    order19_log23_finite_window_uniform_gap R hR
  refine ⟨δ, hδ, ?_⟩
  intro t u ht
  calc
    δ * u ^ 2 ≤
        (momentSplineSymbol 19 (Real.log 2) t ^ 2 +
          momentSplineSymbol 19 (Real.log 3) t ^ 2) * u ^ 2 :=
      mul_le_mul_of_nonneg_right (hgap t ht) (sq_nonneg u)
    _ = (momentSplineSymbol 19 (Real.log 2) t * u) ^ 2 +
        (momentSplineSymbol 19 (Real.log 3) t * u) ^ 2 := by ring

end AEGIS.RHSnowflakeCompactFrameV1

#print axioms AEGIS.RHSnowflakeCompactFrameV1.log23_finite_window_uniform_gap
#print axioms AEGIS.RHSnowflakeCompactFrameV1.order19_log23_finite_window_uniform_gap
#print axioms AEGIS.RHSnowflakeCompactFrameV1.order19_log23_finite_window_frame_bound
