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

import RHPi40V1

/-!
# `π` to eighty digits

The same self-checking chain as `RHPi40V1` (`pi_bound_pow2`), 140 steps at precision `2^{-580}`:

  `3.14159265358979323846264338327950288419716939937510582097494459230781640628620899 < π`
  `π < 3.14159265358979323846264338327950288419716939937510582097494459230781640628620900`.

AUTHORITY_EFFECT = NONE.
-/

namespace AEGIS.RHPi80V1

open Real

theorem pi_gt_d80 :
    (314159265358979323846264338327950288419716939937510582097494459230781640628620899 / 10 ^ 80 : ℝ)
      < π := by
  pi_bound_pow2 lower 140 580

theorem pi_lt_d80 :
    π < (314159265358979323846264338327950288419716939937510582097494459230781640628620900 / 10 ^ 80 : ℝ) := by
  pi_bound_pow2 upper 140 580

end AEGIS.RHPi80V1

#print axioms AEGIS.RHPi80V1.pi_gt_d80
#print axioms AEGIS.RHPi80V1.pi_lt_d80
