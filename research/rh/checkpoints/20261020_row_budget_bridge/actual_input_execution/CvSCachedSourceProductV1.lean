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
/- Cached execution of the remaining actual-input interval products. -/
import CvSCachedColumnV1
namespace AEGIS.CvSCachedSourceProductV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSListIntervalDotV1 AEGIS.CvSCachedColumnV1

theorem mapped_dots_eq {n : ℕ} (hn : 0 < n) (hn' : n ≤ 301)
    (rows : List (Vector n)) (a : Vector n) :
    rows.map (fun row => evalDot row a) =
      (rows.map Vector.values).map (fun row => listDot 96 row a.values) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact evalDot_eq hn hn' row a

/-- A checked staged product identifies every original outward dot entry. -/
theorem product_entry_eq {n r : ℕ} (hn : 0 < n) (hn' : n ≤ 301)
    (rows : List (Vector n)) (fallback a : Vector n) (out : List Iv)
    (hrows : rows.length = r)
    (hc : rows.map (fun row => evalDot row a) = out) (k : Fin r) :
    out.getD k.val ⟨0, 0⟩ = listDot 96 (rows.getD k.val fallback).values a.values := by
  rw [← hc]
  rw [getD_map_lt rows (fun row => evalDot row a) ⟨0, 0⟩ fallback (by omega)]
  exact evalDot_eq hn hn' _ _
end AEGIS.CvSCachedSourceProductV1
#print axioms AEGIS.CvSCachedSourceProductV1.mapped_dots_eq
#print axioms AEGIS.CvSCachedSourceProductV1.product_entry_eq
