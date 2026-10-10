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
# Kernel checks at `t = 31.7` and `t = 35.3` (`p = 192`, `d = 36`, `π` to eighty digits)

AUTHORITY_EFFECT = NONE.
-/

namespace AEGIS.RHZeroChecksAV1

open AEGIS.RHLambdaCheckV1 AEGIS.RHCriticalLineSignV1 AEGIS.RHXiSignV1

theorem lam_a : (lamIv 192 (317 / 10) 26 36 110 22 6 40).hi < 0 := by
  decide +kernel

theorem lam_b : 0 < (lamIv 192 (353 / 10) 26 36 110 22 6 40).lo := by
  decide +kernel

theorem xi_a : (Xi (317 / 10)).re < 0 := by
  have h := xi_neg_of_check (t := 317 / 10) (by norm_num) lam_a
  rwa [show (((317 / 10 : ℚ)) : ℝ) = 317 / 10 by norm_num] at h

theorem xi_b : 0 < (Xi (353 / 10)).re := by
  have h := xi_pos_of_check (t := 353 / 10) (by norm_num) lam_b
  rwa [show (((353 / 10 : ℚ)) : ℝ) = 353 / 10 by norm_num] at h

end AEGIS.RHZeroChecksAV1

#print axioms AEGIS.RHZeroChecksAV1.xi_a
#print axioms AEGIS.RHZeroChecksAV1.xi_b
