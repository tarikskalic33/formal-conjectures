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
import RowBudgetFirstColumnBatch0
open AEGIS.RHFixIntervalV1 AEGIS.CvSFirstColumnCheckerV1
namespace AEGIS.CvSFirstColumnRejectV1
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

/-- Omitting the weighted column cannot produce an accepted certificate. -/
theorem reject_missing_weighted :
    check { AEGIS.RowBudgetFirstColumnBatch0.entry0 with da := [] } = false := by
  decide +kernel

/-- Replacing the positive stored target by the zero interval is rejected. -/
theorem reject_zero_target :
    check { AEGIS.RowBudgetFirstColumnBatch0.entry0 with target := ⟨0, 0⟩ } = false := by
  decide +kernel

end AEGIS.CvSFirstColumnRejectV1
#print axioms AEGIS.CvSFirstColumnRejectV1.reject_missing_weighted
#print axioms AEGIS.CvSFirstColumnRejectV1.reject_zero_target
