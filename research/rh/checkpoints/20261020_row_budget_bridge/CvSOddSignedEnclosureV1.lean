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
/- Transport positive-frequency enclosures through a proved oddness identity. -/
import Mathlib.Analysis.Complex.Norm

namespace AEGIS.CvSOddSignedEnclosureV1

def lower (lo hi : ℕ → ℝ) (k : ℤ) : ℝ :=
  if k < 0 then -hi k.natAbs else if k = 0 then 0 else lo k.natAbs

def upper (lo hi : ℕ → ℝ) (k : ℤ) : ℝ :=
  if k < 0 then -lo k.natAbs else if k = 0 then 0 else hi k.natAbs

/-- Negative frequencies reverse and negate both endpoints; zero is handled exactly. -/
theorem signed_enclosure (t : ℤ → ℝ) (lo hi : ℕ → ℝ) (N : ℕ)
    (hzero : t 0 = 0) (hodd : ∀ k, t (-k) = -t k)
    (hpos : ∀ n : ℕ, 1 ≤ n → n ≤ N → lo n ≤ t n ∧ t n ≤ hi n)
    (k : ℤ) (hk : k.natAbs ≤ N) :
    lower lo hi k ≤ t k ∧ t k ≤ upper lo hi k := by
  by_cases hz : k = 0
  · subst k
    simp [lower, upper, hzero]
  by_cases hn : k < 0
  · have ha : (k.natAbs : ℤ) = -k := by rw [Int.natCast_natAbs, abs_of_neg hn]
    have h1 : 1 ≤ k.natAbs := by omega
    have hb := hpos k.natAbs h1 hk
    have ht : t k = -t (k.natAbs : ℤ) := by
      rw [ha, hodd, neg_neg]
    simp only [lower, upper, if_pos hn]
    rw [ht]
    constructor <;> linarith [hb.1, hb.2]
  · have ha : (k.natAbs : ℤ) = k := by
      rw [Int.natCast_natAbs, abs_of_nonneg (le_of_not_gt hn)]
    have h1 : 1 ≤ k.natAbs := by omega
    have hb := hpos k.natAbs h1 hk
    rw [ha] at hb
    simpa only [lower, upper, if_neg hn, if_neg hz] using hb

/-- Rational source boxes retain the same signed endpoint convention after casting. -/
theorem signed_rational_bounds (t : ℤ → ℝ) (lo hi : ℕ → ℚ) (N : ℕ)
    (hzero : t 0 = 0) (hodd : ∀ k, t (-k) = -t k)
    (hpos : ∀ n : ℕ, 1 ≤ n → n ≤ N → (lo n : ℝ) ≤ t n ∧ t n ≤ (hi n : ℝ))
    (k : ℤ) (hk : k.natAbs ≤ N) :
    ((if k < 0 then -hi k.natAbs else if k = 0 then 0 else lo k.natAbs : ℚ) : ℝ) ≤ t k ∧
      t k ≤ ((if k < 0 then -lo k.natAbs else if k = 0 then 0 else hi k.natAbs : ℚ) : ℝ) := by
  have h := signed_enclosure t (fun n => (lo n : ℝ)) (fun n => (hi n : ℝ)) N
    hzero hodd hpos k hk
  by_cases hn : k < 0
  · simpa [lower, upper, hn] using h
  · by_cases hz : k = 0
    · simpa [lower, upper, hn, hz] using h
    · simpa [lower, upper, hn, hz] using h

end AEGIS.CvSOddSignedEnclosureV1
#print axioms AEGIS.CvSOddSignedEnclosureV1.signed_enclosure

#print axioms AEGIS.CvSOddSignedEnclosureV1.signed_rational_bounds
