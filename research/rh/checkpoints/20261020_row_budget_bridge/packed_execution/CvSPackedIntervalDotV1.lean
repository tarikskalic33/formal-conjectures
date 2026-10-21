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
/- Reuse the existing signed Kronecker dot proof; preserve all interval endpoints. -/
import CvSPackedGramV1
import CvSListIntervalDotV1
namespace AEGIS.CvSPackedIntervalDotV1
open Finset AEGIS.RHFixIntervalV1 AEGIS.CvSPackedGramV1
open AEGIS.CvSIntervalMatrixProductV1 AEGIS.CvSListIntervalDotV1

def intDot (a b : List ℤ) : ℤ := (List.zipWith (fun x y => x * y) a b).sum

theorem intDot_eq_range (a b : List ℤ) (h : b.length = a.length) :
    intDot a b = ∑ k ∈ range a.length, a.getD k 0 * b.getD k 0 := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [intDot]
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      have hy : ys.length = xs.length := by simpa using h
      change x * y + intDot xs ys = _
      rw [ih ys hy, List.length_cons, sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      ring

def packedDot (base bound : ℕ) (a b : List ℤ) : ℤ :=
  gramEntry base bound a.length (pack base (offRow bound a)) a.sum
    (pack base (offRow bound b).reverse) b.sum

/-- Signed entries, length and carry bound are explicit; no finite-width overflow. -/
theorem packedDot_eq (base bound : ℕ) (a b : List ℤ)
    (hn : 0 < a.length) (hlen : b.length = a.length)
    (ha : ∀ x ∈ a, -(bound : ℤ) ≤ x ∧ x ≤ bound)
    (hb : ∀ x ∈ b, -(bound : ℤ) ≤ x ∧ x ≤ bound)
    (hcarry : a.length * a.length * (2 * bound * (2 * bound)) < base) :
    packedDot base bound a b = intDot a b := by
  exact (gramEntry_eq hn hlen ha hb hcarry).trans (intDot_eq_range a b hlen).symm

def bounded (bound : ℕ) (a : List Iv) : Prop :=
  ∀ x ∈ a, (-(bound : ℤ) ≤ mid x ∧ mid x ≤ bound) ∧
    (-(bound : ℤ) ≤ |mid x| ∧ |mid x| ≤ bound) ∧
    (-(bound : ℤ) ≤ rad x ∧ rad x ≤ bound)

def packedIntervalDot (p base bound : ℕ) (a b : List Iv) : Iv :=
  let c := packedDot base bound (a.map mid) (b.map mid)
  let r := packedDot base bound (a.map (fun x => |mid x|)) (b.map rad) +
    packedDot base bound (a.map rad) (b.map (fun x => |mid x|)) +
    packedDot base bound (a.map rad) (b.map rad)
  ⟨fdiv p (c - r), cdiv p (c + r)⟩

theorem component_bound (bound : ℕ) (a : List Iv)
    (f : Iv → ℤ) (hf : ∀ x ∈ a, -(bound : ℤ) ≤ f x ∧ f x ≤ bound) :
    ∀ z ∈ a.map f, -(bound : ℤ) ≤ z ∧ z ≤ bound := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
  exact hf x hx

theorem radius_split (a b : List Iv) :
    (List.zipWith (fun x y => |mid x| * rad y + rad x * |mid y| + rad x * rad y) a b).sum =
      intDot (a.map (fun x => |mid x|)) (b.map rad) +
      intDot (a.map rad) (b.map (fun x => |mid x|)) +
      intDot (a.map rad) (b.map rad) := by
  induction a generalizing b with
  | nil => simp [intDot]
  | cons x xs ih =>
    cases b with
    | nil => simp [intDot]
    | cons y ys =>
      simp only [List.zipWith_cons_cons, List.sum_cons, List.map_cons]
      rw [ih ys]
      simp only [intDot, List.zipWith_cons_cons, List.sum_cons]
      ring

/-- The packed evaluator equals the original midpoint-radius list evaluator exactly. -/
theorem packedIntervalDot_eq (p base bound : ℕ) (a b : List Iv)
    (hn : 0 < a.length) (hlen : b.length = a.length)
    (ha : bounded bound a) (hb : bounded bound b)
    (hcarry : a.length * a.length * (2 * bound * (2 * bound)) < base) :
    packedIntervalDot p base bound a b = listDot p a b := by
  have hp (f g : Iv → ℤ)
      (hf : ∀ x ∈ a, -(bound : ℤ) ≤ f x ∧ f x ≤ bound)
      (hg : ∀ x ∈ b, -(bound : ℤ) ≤ g x ∧ g x ≤ bound) :
      packedDot base bound (a.map f) (b.map g) = intDot (a.map f) (b.map g) := by
    apply packedDot_eq
    · simpa using hn
    · simpa using hlen
    · exact component_bound bound a f hf
    · exact component_bound bound b g hg
    · simpa using hcarry
  unfold packedIntervalDot
  rw [hp mid mid (fun x hx => (ha x hx).1) (fun x hx => (hb x hx).1),
    hp (fun x => |mid x|) rad (fun x hx => (ha x hx).2.1) (fun x hx => (hb x hx).2.2),
    hp rad (fun x => |mid x|) (fun x hx => (ha x hx).2.2) (fun x hx => (hb x hx).2.1),
    hp rad rad (fun x hx => (ha x hx).2.2) (fun x hx => (hb x hx).2.2),
    ← radius_split]
  simp only [listDot, intDot, List.zipWith_map]

structure PackedRow where
  forward : ℕ
  reverse : ℕ
  total : ℤ
  length : ℕ
  deriving DecidableEq

def prepareRow (base bound : ℕ) (r : List ℤ) : PackedRow :=
  ⟨pack base (offRow bound r), pack base (offRow bound r).reverse, r.sum, r.length⟩

def cachedDot (base bound : ℕ) (a b : PackedRow) : ℤ :=
  gramEntry base bound a.length a.forward a.total b.reverse b.total

structure PackedIntervalRow where
  middle : PackedRow
  absolute : PackedRow
  radius : PackedRow
  deriving DecidableEq

def prepareInterval (base bound : ℕ) (a : List Iv) : PackedIntervalRow :=
  ⟨prepareRow base bound (a.map mid), prepareRow base bound (a.map (fun x => |mid x|)),
    prepareRow base bound (a.map rad)⟩

def cachedIntervalDot (p base bound : ℕ) (a b : PackedIntervalRow) : Iv :=
  let c := cachedDot base bound a.middle b.middle
  let r := cachedDot base bound a.absolute b.radius +
    cachedDot base bound a.radius b.absolute + cachedDot base bound a.radius b.radius
  ⟨fdiv p (c - r), cdiv p (c + r)⟩

/-- Exact cached packing can be shared by every matrix entry using a row. -/
theorem cachedIntervalDot_prepare_eq (p base bound : ℕ) (a b : List Iv) :
    cachedIntervalDot p base bound (prepareInterval base bound a) (prepareInterval base bound b) =
      packedIntervalDot p base bound a b := rfl

/-- Cached witnesses are trusted only after their exact preparation identities. -/
theorem cachedIntervalDot_eq (p base bound : ℕ) (a b : List Iv)
    (A B : PackedIntervalRow) (hA : A = prepareInterval base bound a)
    (hB : B = prepareInterval base bound b)
    (hn : 0 < a.length) (hlen : b.length = a.length)
    (ha : bounded bound a) (hb : bounded bound b)
    (hcarry : a.length * a.length * (2 * bound * (2 * bound)) < base) :
    cachedIntervalDot p base bound A B = listDot p a b := by
  rw [hA, hB, cachedIntervalDot_prepare_eq]
  exact packedIntervalDot_eq p base bound a b hn hlen ha hb hcarry

end AEGIS.CvSPackedIntervalDotV1
#print axioms AEGIS.CvSPackedIntervalDotV1.packedDot_eq
#print axioms AEGIS.CvSPackedIntervalDotV1.packedIntervalDot_eq
#print axioms AEGIS.CvSPackedIntervalDotV1.cachedIntervalDot_prepare_eq
#print axioms AEGIS.CvSPackedIntervalDotV1.cachedIntervalDot_eq
#check @AEGIS.CvSPackedIntervalDotV1.packedIntervalDot_eq
