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
/- Reproduce and repair the exact source-row distribution failure. -/
import Mathlib.Data.Complex.BigOperators
open scoped BigOperators
namespace AEGIS.SourceRowDistributionV1

theorem distribute_source_row {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : κ → ι → ℝ) (K : κ → ℝ) (v : ι → ℂ) :
    (∑ i, ((∑ k, X k i * K k : ℝ) : ℂ) * v i) =
      ∑ i, ∑ k, ((X k i : ℂ) * (K k : ℂ)) * v i := by
  fail_if_success solve | simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
end AEGIS.SourceRowDistributionV1
#print axioms AEGIS.SourceRowDistributionV1.distribute_source_row
