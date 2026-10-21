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
/-! ## Strict evaluation and list lemmas

The kernel reduces lazily; `fN`, `fI`, `fL`, `fP` force a value to a literal once (continuation
style) and are definitionally the identity (`fN_eq`, `fI_eq`, `fL_eq`, `fP_eq`). -/

def fN {α : Sort _} (n : ℕ) (k : ℕ → α) : α :=
  match n with
  | 0 => k 0
  | m + 1 => k (Nat.succ m)

def fI {α : Sort _} (e : ℤ) (k : ℤ → α) : α :=
  match e with
  | .ofNat n => fN n fun n' => k (.ofNat n')
  | .negSucc n => fN n fun n' => k (.negSucc n')

def fL {α : Sort _} : List ℤ → (List ℤ → α) → α
  | [], k => k []
  | a :: l, k => fI a fun a' => fL l fun l' => k (a' :: l')

def fP {α : Sort _} : List (ℕ × ℤ) → (List (ℕ × ℤ) → α) → α
  | [], k => k []
  | (a, s) :: l, k => fN a fun a' => fI s fun s' => fP l fun l' => k ((a', s') :: l')

theorem fN_eq {α : Sort _} (n : ℕ) (k : ℕ → α) : fN n k = k n := by cases n <;> rfl

theorem fI_eq {α : Sort _} (e : ℤ) (k : ℤ → α) : fI e k = k e := by
  cases e <;> simp only [fI, fN_eq]

theorem fL_eq {α : Sort _} (l : List ℤ) (k : List ℤ → α) : fL l k = k l := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih => simp only [fL, fI_eq, ih]

theorem fP_eq {α : Sort _} (l : List (ℕ × ℤ)) (k : List (ℕ × ℤ) → α) : fP l k = k l := by
  induction l generalizing k with
  | nil => rfl
  | cons p l ih => obtain ⟨a, s⟩ := p; simp only [fP, fN_eq, fI_eq, ih]

/-- Fuel-driven transpose: row `i` of the result is column `i` of `rows`. -/
def trans {α : Type} (d : α) : ℕ → List (List α) → List (List α)
  | 0, _ => []
  | n + 1, rows => rows.map (fun r => r.headD d) :: trans d n (rows.map List.tail)

theorem getD_tail {α : Type} (l : List α) (d : α) (i : ℕ) : l.tail.getD i d = l.getD (i + 1) d := by
  cases l <;> simp

theorem headD_eq {α : Type} (l : List α) (d : α) : l.headD d = l.getD 0 d := by
  cases l <;> simp

theorem getD_map_lt {α β : Type} (l : List α) (f : α → β) (d : β) (e : α) {m : ℕ}
    (hm : m < l.length) : (l.map f).getD m d = f (l.getD m e) := by
  simp [List.getD_eq_getElem?_getD, hm]

theorem trans_length {α : Type} (d : α) : ∀ n rows, (trans d n rows).length = n
  | 0, _ => rfl
  | n + 1, rows => by simp [trans, trans_length d n]

theorem trans_row_length {α : Type} (d : α) : ∀ (n : ℕ) (rows : List (List α)) (i : ℕ), i < n →
    ((trans d n rows).getD i []).length = rows.length
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, rows, 0, _ => by simp [trans]
  | n + 1, rows, i + 1, hi => by
      simp only [trans, List.getD_cons_succ]
      rw [trans_row_length d n _ i (by omega), List.length_map]

theorem trans_getD {α : Type} (d : α) : ∀ (n : ℕ) (rows : List (List α)) (i m : ℕ), i < n →
    m < rows.length → ((trans d n rows).getD i []).getD m d = (rows.getD m []).getD i d
  | 0, _, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | n + 1, rows, 0, m, _, hm => by
      simp only [trans, List.getD_cons_zero]
      rw [getD_map_lt _ _ _ [] hm, headD_eq]
  | n + 1, rows, i + 1, m, hi, hm => by
      simp only [trans, List.getD_cons_succ]
      rw [trans_getD d n _ i m (by omega) (by simpa using hm), getD_map_lt _ _ _ [] hm, getD_tail]

/-- Second differences `2 b - a - c`. -/
def sd : List ℤ → List ℤ
  | a :: b :: c :: t => (2 * b - a - c) :: sd (b :: c :: t)
  | _ => []

theorem sd_length : ∀ l : List ℤ, (sd l).length = l.length - 2
  | a :: b :: c :: t => by simp [sd, sd_length (b :: c :: t)]
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl

theorem sd_getD : ∀ (l : List ℤ) (k : ℕ), k + 2 < l.length →
    (sd l).getD k 0 = 2 * l.getD (k + 1) 0 - l.getD k 0 - l.getD (k + 2) 0
  | a :: b :: c :: t, 0, _ => by simp [sd]
  | a :: b :: c :: t, k + 1, hk => by
      simp only [sd, List.getD_cons_succ]
      rw [sd_getD (b :: c :: t) k (by simp at hk ⊢; omega)]
      simp
  | [], _, hk => by simp at hk
  | [_], _, hk => by simp at hk
  | [_, _], _, hk => by simp at hk

theorem getD_zipWith {f : ℤ → ℤ → ℤ} {a b : List ℤ} {k : ℕ} (ha : k < a.length)
    (hb : k < b.length) : (List.zipWith f a b).getD k 0 = f (a.getD k 0) (b.getD k 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem ha,
    List.getElem?_eq_getElem hb]

theorem getD_append_lt {a b : List ℤ} {k : ℕ} (h : k < a.length) :
    (a ++ b).getD k 0 = a.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_ge {a b : List ℤ} {k : ℕ} (h : a.length ≤ k) :
    (a ++ b).getD k 0 = b.getD (k - a.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem pad_getD (c : List ℤ) (t : ℕ) :
    (0 :: 0 :: (c ++ [0, 0])).getD t 0 = if 2 ≤ t then c.getD (t - 2) 0 else 0 := by
  rcases t with _ | _ | t
  · simp
  · simp
  · simp only [List.getD_cons_succ, show 2 ≤ t + 2 by omega, if_true, show t + 2 - 2 = t by omega]
    by_cases h : t < c.length
    · exact getD_append_lt h
    · rw [getD_append_ge (by omega), List.getD_eq_default _ _ (by omega : c.length ≤ t)]
      rcases t - c.length with _ | _ | _ <;> simp

theorem getD_drop {α : Type} (l : List α) (d : α) (n m : ℕ) : (l.drop n).getD m d = l.getD (n + m) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
