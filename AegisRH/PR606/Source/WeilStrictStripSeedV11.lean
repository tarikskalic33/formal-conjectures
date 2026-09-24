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


import WeilOffLineSeedV10
import WeilMomentAnnihilatorV1
import Mathlib.Tactic

/-!
AEGIS Ω — strict-strip Mellin seed V11.

The original V11 construction built a fresh local bump near x = 1. The
current proof surface is strictly smaller: the already-verified V10 off-line
seed theorem constructs one compact-smooth packet whose Mellin transform is
nonzero at any two prescribed complex points, with no strip restriction.

For strict-strip points, composing that stronger seed with the exact
WeilMomentAnnihilatorV1 enforces the two repository moment conditions while
preserving both nonzero Mellin evaluations.

AUTHORITY_EFFECT = NONE.
-/

open Complex
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilStrictStripSeedV11

open AEGIS.WeilOffLineSeedV10

/-- A single compact-smooth packet can detect two arbitrary prescribed complex
points. This is inherited from the stronger exact V10 seed producer. -/
theorem exists_compact_smooth_seed_two_mellin_ne_zero_v11
    (s₁ s₂ : ℂ) :
    ∃ f : WeilCompactSmoothGV1,
      mellin f.1 s₁ ≠ 0 ∧ mellin f.1 s₂ ≠ 0 := by
  exact exists_packet_mellin_ne_zero_pair_v10 s₁ s₂

/-- For any two points in the strict critical strip, there is an exact
repository moment-zero packet whose Mellin transform is nonzero at both
points. -/
theorem exists_moment_zero_seed_two_strip_points_v11
    (s₁ s₂ : ℂ)
    (h10 : 0 < s₁.re) (h11 : s₁.re < 1)
    (h20 : 0 < s₂.re) (h21 : s₂.re < 1) :
    ∃ g : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 g ∧
      mellin g.1 s₁ ≠ 0 ∧
      mellin g.1 s₂ ≠ 0 := by
  obtain ⟨f, hf1, hf2⟩ :=
    exists_compact_smooth_seed_two_mellin_ne_zero_v11 s₁ s₂
  refine ⟨WeilMomentAnnihilatorV1 f,
    weil_moment_annihilator_moments_v1 f, ?_, ?_⟩
  · exact
      weil_moment_annihilator_mellin_ne_zero_v1
        f h10 h11 hf1
  · exact
      weil_moment_annihilator_mellin_ne_zero_v1
        f h20 h21 hf2

end AEGIS.WeilStrictStripSeedV11

#print axioms AEGIS.WeilStrictStripSeedV11.exists_compact_smooth_seed_two_mellin_ne_zero_v11
#print axioms AEGIS.WeilStrictStripSeedV11.exists_moment_zero_seed_two_strip_points_v11
