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
/- Fail closed when the actual cross kernel's 2*pi normalization is omitted. -/
import CvSSourceQAllV1
namespace AEGIS.CvSSourceQRejectV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSCachedColumnV1 AEGIS.CvSIntervalMatrixProductV1
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem reject_missing_inverse_two_pi :
    contains (AEGIS.CvSFullTableClosureV1.Q 0 0)
      (evalDot (AEGIS.CvSSourceProductAllV1.inputColumn 0).x
        (AEGIS.CvSSourceQAllV1.vector 0)) = false := by decide +kernel
end AEGIS.CvSSourceQRejectV1
#print axioms AEGIS.CvSSourceQRejectV1.reject_missing_inverse_two_pi
