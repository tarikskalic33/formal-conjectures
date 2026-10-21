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

import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! A uniform obstruction to an absolute Schur certificate on repeated atoms.
This is generic finite-dimensional ordered-field mathematics. It supplies no
analytic estimate for the actual Weil pairing and assumes no RH statement. -/

open scoped BigOperators

namespace AEGIS.RouteC.SignedCliqueObstruction

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- An off-diagonal clique of costs at least d forces every common weighted
row ceiling to be at least n*d. Positive weights cannot cure dimension growth. -/
theorem clique_floor_le_weighted_ceiling
    (n : ℕ) (c : Fin (n + 1) → Fin (n + 1) → α)
    (w : Fin (n + 1) → α) (d S : α)
    (hd : 0 ≤ d) (hw : ∀ i, 0 < w i)
    (hfloor : ∀ i j, i ≠ j → d ≤ c i j)
    (hrow : ∀ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
      c i j * (w j / w i) ≤ S) :
    (n : α) * d ≤ S := by
  classical
  obtain ⟨i, _, hmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset (Fin (n + 1))) w Finset.univ_nonempty
  have hcost : ∀ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
      d ≤ c i j * (w j / w i) := by
    intro j hj
    have hij : i ≠ j := Ne.symm (Finset.ne_of_mem_erase hj)
    have hratio : 1 ≤ w j / w i := by
      apply (le_div_iff₀ (hw i)).mpr
      simpa using hmin j (Finset.mem_univ j)
    calc
      d ≤ c i j := hfloor i j hij
      _ = c i j * 1 := (mul_one _).symm
      _ ≤ c i j * (w j / w i) :=
        mul_le_mul_of_nonneg_left hratio (hd.trans (hfloor i j hij))
  have hsum := Finset.sum_le_sum hcost
  have hcard : (∑ _j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, d) =
      (n : α) * d := by simp
  rw [hcard] at hsum
  exact hsum.trans (hrow i)

/-- Exact Q16.16 obstruction for any clique, with the reported optimized
row ceiling. This is arithmetic admission, not a claim about actual entries. -/
theorem q16_clique_admission
    (n : ℕ) (c : Fin (n + 1) → Fin (n + 1) → α)
    (w : Fin (n + 1) → α) (q : α)
    (hq : 0 ≤ q) (hw : ∀ i, 0 < w i)
    (hfloor : ∀ i j, i ≠ j → q / 65536 ≤ c i j)
    (hrow : ∀ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
      c i j * (w j / w i) ≤ 46688 / 65536) :
    (n : α) * q ≤ 46688 := by
  have h := clique_floor_le_weighted_ceiling n c w
    (q / 65536) (46688 / 65536) (div_nonneg hq (by norm_num)) hw hfloor hrow
  linarith

/-- A negative rank-one Gram is nonpositive for every finite dimension and
every real amplitude. The absolute off-diagonal row budget can nevertheless
grow linearly in dimension, as the preceding obstruction proves. -/
theorem signed_rank_one_nonpositive {ι : Type*} [Fintype ι]
    (a : α) (ha : 0 ≤ a) (z : ι → α) :
    (∑ i, ∑ j, -a * z i * z j) ≤ 0 := by
  have hid : (∑ i, ∑ j, -a * z i * z j) =
      -a * ((∑ i, z i) * (∑ i, z i)) := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]
  rw [hid]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (mul_self_nonneg _)

#print axioms clique_floor_le_weighted_ceiling
#print axioms q16_clique_admission
#print axioms signed_rank_one_nonpositive
#check @clique_floor_le_weighted_ceiling
#check @q16_clique_admission
#check @signed_rank_one_nonpositive

end AEGIS.RouteC.SignedCliqueObstruction
