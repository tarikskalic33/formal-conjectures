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
/-
AEGIS Omega — source-bound symmetry composition for the existing CvS projected Gram.
Additive, read-only Lean candidate for formal-conjectures@cf9372f1.
Imports the previously generated projected packed certificate candidate.
No sorry, admit, axioms, native_decide, or hypothesis of RH.

Kernel compilation remains NOT RUN; no new GitHub workflow is claimed.
-/
import CvSProjectedPackedCertificateL12V1
import CvSRowTailV1

open Finset

namespace AEGIS.CvSProjectedSymmetryV1

open AEGIS.CvSProjectedPackedCertificateL12V1
open AEGIS.CvSPackedGramV1
open AEGIS.RHFixIntervalV1

/-- Inherited symmetry of the actual source CvS entry, at L = 6/5. -/
theorem signedEntry_symm (M : ℕ) (k l : Fin 141) :
    signedEntry M k l = signedEntry M l k := by
  unfold signedEntry
  exact AEGIS.CvSRowTailV1.cvsEntry_symm M
    (by norm_num : (0 : ℝ) < 6 / 5) (signedFreq k) (signedFreq l)

/-- Congruence by an arbitrary real transform preserves matrix symmetry.
    No numeric interval membership or positive definiteness is needed. -/
theorem projectedEntry_symm (M : ℕ) (i j : Fin 139) :
    projectedEntry M i j = projectedEntry M j i := by
  classical
  unfold projectedEntry
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [signedEntry_symm M k l]
  ring

/-- A direct use of the existing packed certificate, with the symmetry
    hypothesis discharged from the source. Source interval membership remains
    a separately stated analytic obligation. -/
theorem projected_lower_of_Iv {M : ℕ}
    (hIv : ∀ i j : Fin 139,
      (Im certI i.val j.val).Mem certQ (projectedEntry M i j))
    (c : Fin 139 → ℂ) :
    ((certEps - certEta : ℤ) : ℝ) * ∑ i, ‖c i‖ ^ 2 ≤
      2 ^ certQ * (∑ i, ∑ j,
        c i * (starRingEnd ℂ) (c j) * (projectedEntry M i j : ℂ)).re := by
  exact projected_lower (M := M) (projectedEntry_symm M) hIv c

/-- Positive semidefiniteness in the 139-dimensional transformed atom
    image, conditional on the true analytic interval membership. -/
theorem projected_nonnegative_of_Iv {M : ℕ}
    (hIv : ∀ i j : Fin 139,
      (Im certI i.val j.val).Mem certQ (projectedEntry M i j))
    (c : Fin 139 → ℂ) :
    0 ≤ (∑ i, ∑ j,
      c i * (starRingEnd ℂ) (c j) * (projectedEntry M i j : ℂ)).re := by
  exact projected_nonnegative (M := M) (projectedEntry_symm M) hIv c

end AEGIS.CvSProjectedSymmetryV1

#print axioms AEGIS.CvSProjectedSymmetryV1.signedEntry_symm
#print axioms AEGIS.CvSProjectedSymmetryV1.projectedEntry_symm
#print axioms AEGIS.CvSProjectedSymmetryV1.projected_lower_of_Iv
#print axioms AEGIS.CvSProjectedSymmetryV1.projected_nonnegative_of_Iv