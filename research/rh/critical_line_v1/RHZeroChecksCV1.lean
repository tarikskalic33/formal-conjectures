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

import RHXiSignV1

/-!
# Kernel checks at `t = 45.7` and `t = 48.9` (`p = 192`, `d = 36`, `π` to eighty digits)

AUTHORITY_EFFECT = NONE.
-/

namespace AEGIS.RHZeroChecksCV1

open AEGIS.RHLambdaCheckV1 AEGIS.RHCriticalLineSignV1 AEGIS.RHXiSignV1

theorem lam_a : (lamIv 192 (457 / 10) 26 36 110 22 6 40).hi < 0 := by
  decide +kernel

theorem lam_b : 0 < (lamIv 192 (489 / 10) 26 36 110 22 6 40).lo := by
  decide +kernel

theorem xi_a : (Xi (457 / 10)).re < 0 := by
  have h := xi_neg_of_check (t := 457 / 10) (by norm_num) lam_a
  rwa [show (((457 / 10 : ℚ)) : ℝ) = 457 / 10 by norm_num] at h

theorem xi_b : 0 < (Xi (489 / 10)).re := by
  have h := xi_pos_of_check (t := 489 / 10) (by norm_num) lam_b
  rwa [show (((489 / 10 : ℚ)) : ℝ) = 489 / 10 by norm_num] at h

end AEGIS.RHZeroChecksCV1

#print axioms AEGIS.RHZeroChecksCV1.xi_a
#print axioms AEGIS.RHZeroChecksCV1.xi_b
