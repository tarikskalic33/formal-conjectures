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
/- Outward integer division used by the actual CvS divided-difference rows. -/
import RHFixIntervalV1
namespace AEGIS.CvSIntervalDivideV1
open AEGIS.RHFixIntervalV1

def divPos (I : Iv) (d : ℤ) : Iv := ⟨I.lo / d, -((-I.hi) / d)⟩

theorem divPos_mem (p : ℕ) {I : Iv} {x : ℝ} (hx : I.Mem p x) {d : ℤ}
    (hd : 0 < d) : (divPos I d).Mem p (x / (d : ℝ)) := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hf : ((I.lo / d : ℤ) : ℝ) * (d : ℝ) ≤ (I.lo : ℝ) := by
    exact_mod_cast Int.ediv_mul_le I.lo (ne_of_gt hd)
  have hc : (((-I.hi) / d : ℤ) : ℝ) * (d : ℝ) ≤ -(I.hi : ℝ) := by
    exact_mod_cast Int.ediv_mul_le (-I.hi) (ne_of_gt hd)
  constructor
  · change ((I.lo / d : ℤ) : ℝ) / 2 ^ p ≤ x / (d : ℝ)
    exact (div_le_div_iff₀ hp hdR).2 (hf.trans ((div_le_iff₀ hp).1 hx.1))
  · change x / (d : ℝ) ≤ ((-((-I.hi) / d) : ℤ) : ℝ) / 2 ^ p
    apply (div_le_div_iff₀ hdR hp).2
    simp only [Int.cast_neg]
    have hu := (le_div_iff₀ hp).1 hx.2
    linarith

def divInt (I : Iv) (d : ℤ) : Iv :=
  if d < 0 then (divPos I (-d)).neg else divPos I d

/-- A negative divisor reverses and negates the endpoints. -/
theorem divInt_mem (p : ℕ) {I : Iv} {x : ℝ} (hx : I.Mem p x) {d : ℤ}
    (hd : d ≠ 0) : (divInt I d).Mem p (x / (d : ℝ)) := by
  by_cases hn : d < 0
  · rw [divInt, if_pos hn]
    have h := Iv.mem_neg p (divPos_mem p hx (neg_pos.mpr hn))
    simpa only [Int.cast_neg, div_neg, neg_neg] using h
  · rw [divInt, if_neg hn]
    exact divPos_mem p hx (by omega)

end AEGIS.CvSIntervalDivideV1
#print axioms AEGIS.CvSIntervalDivideV1.divPos_mem
#print axioms AEGIS.CvSIntervalDivideV1.divInt_mem
#check @AEGIS.CvSIntervalDivideV1.divInt_mem
