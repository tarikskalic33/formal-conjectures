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
# `π` to forty digits

`3.1415926535897932384626433832795028841971 < π < 3.1415926535897932384626433832795028841972`.

The proof is Mathlib's `sqrtTwoAddSeries` chain (`pi_lower_bound_start`, `sqrtTwoAddSeries_step_up`,
`pi_upper_bound_start`, `sqrtTwoAddSeries_step_down`), as in `Real.pi_gt_d20`.  The witnesses are not
typed in: `pi_bound_pow2` computes them, `X_{i+1} = ⌈√((2·2^P + X_i)·2^P)⌉` for the lower bound and `⌊·⌋`
for the upper bound (numerators over `2^P`), and every step is then checked by `norm_num`.  The
generator is untrusted: a wrong witness only makes the proof fail.  `picert.py` is its exact mirror.
AUTHORITY_EFFECT = NONE.
-/

namespace AEGIS.RHPi40V1

open Real Lean Elab Tactic

/-- `⌈√v⌉`. -/
def sqrtUp (v : ℕ) : ℕ := if Nat.sqrt v * Nat.sqrt v = v then Nat.sqrt v else Nat.sqrt v + 1

/-- The witness numerators over `2^P`, rounded up (`up`) or down. -/
def chain (up : Bool) (P : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, X =>
    let v := (2 * 2 ^ P + X) * 2 ^ P
    let r := if up then sqrtUp v else Nat.sqrt v
    r :: chain up P k r

/-- `pi_bound_pow2 lower n P` proves `a < π` and `pi_bound_pow2 upper n P` proves `π < a` with the
`sqrtTwoAddSeries` chain of length `n` at precision `2^{-P}`. -/
elab "pi_bound_pow2 " dir:ident n:num P:num : tactic => do
  let n := n.getNat
  let P := P.getNat
  let up := dir.getId == `lower
  if up then
    evalTactic (← `(tactic| apply pi_lower_bound_start $(quote n)))
  else
    evalTactic (← `(tactic| apply pi_upper_bound_start $(quote n)))
  for X in chain up P n 0 do
    if up then
      evalTactic (← `(tactic| apply sqrtTwoAddSeries_step_up $(quote X) $(quote (2 ^ P))))
    else
      evalTactic (← `(tactic| apply sqrtTwoAddSeries_step_down $(quote X) $(quote (2 ^ P))))
  evalTactic (← `(tactic| simp [sqrtTwoAddSeries]))
  allGoals <| evalTactic (← `(tactic| norm_num1))

theorem pi_gt_d40 : (31415926535897932384626433832795028841971 / 10 ^ 40 : ℝ) < π := by
  pi_bound_pow2 lower 72 290

theorem pi_lt_d40 : π < (31415926535897932384626433832795028841972 / 10 ^ 40 : ℝ) := by
  pi_bound_pow2 upper 72 290

end AEGIS.RHPi40V1

#print axioms AEGIS.RHPi40V1.pi_gt_d40
#print axioms AEGIS.RHPi40V1.pi_lt_d40
