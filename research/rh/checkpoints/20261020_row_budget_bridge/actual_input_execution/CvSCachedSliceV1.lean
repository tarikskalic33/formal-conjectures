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
/- Source indexing of the 141 inner rows inside the 301-row cross product. -/
import CvSCachedSourceProductV1
namespace AEGIS.CvSCachedSliceV1
open AEGIS.RHFixIntervalV1

theorem inner_slice (ys : List Iv) (k : Fin 141) :
    ((ys.drop 80).take 141).getD k.val ⟨0, 0⟩ = ys.getD (k.val + 80) ⟨0, 0⟩ := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, k.isLt,
    Nat.add_comm]
end AEGIS.CvSCachedSliceV1
#print axioms AEGIS.CvSCachedSliceV1.inner_slice
