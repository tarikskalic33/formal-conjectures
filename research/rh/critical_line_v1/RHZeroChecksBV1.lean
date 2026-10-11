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
# Kernel checks at `t = 39.3` and `t = 42.2` (`p = 192`, `d = 36`, `π` to eighty digits)

AUTHORITY_EFFECT = NONE.
-/

namespace AEGIS.RHZeroChecksBV1

open AEGIS.RHLambdaCheckV1 AEGIS.RHCriticalLineSignV1 AEGIS.RHXiSignV1

theorem lam_a : (lamIv 192 (393 / 10) 26 36 110 22 6 40).hi < 0 := by
  decide +kernel

theorem lam_b : 0 < (lamIv 192 (422 / 10) 26 36 110 22 6 40).lo := by
  decide +kernel

theorem xi_a : (Xi (393 / 10)).re < 0 := by
  have h := xi_neg_of_check (t := 393 / 10) (by norm_num) lam_a
  rwa [show (((393 / 10 : ℚ)) : ℝ) = 393 / 10 by norm_num] at h

theorem xi_b : 0 < (Xi (422 / 10)).re := by
  have h := xi_pos_of_check (t := 422 / 10) (by norm_num) lam_b
  rwa [show (((422 / 10 : ℚ)) : ℝ) = 422 / 10 by norm_num] at h

end AEGIS.RHZeroChecksBV1

#print axioms AEGIS.RHZeroChecksBV1.xi_a
#print axioms AEGIS.RHZeroChecksBV1.xi_b
