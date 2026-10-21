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

/-! ## Soundness of the strict check (no hypotheses) -/

theorem certR_length : certR.length = 139 := by decide +kernel

theorem AD_length : AD.length = 139 := by decide +kernel
theorem AT_length : AT.length = 139 := by decide +kernel
theorem BT_length : BT.length = 139 := by decide +kernel

theorem colR_length {i : ℕ} (hi : i < 139) : (colR i).length = 139 := by
  rw [colR, trans_row_length 0 139 certR i hi, certR_length]

theorem colR_getD {i : ℕ} (hi : i < 139) (m : ℕ) : (colR i).getD m 0 = rI m i := by
  by_cases hm : m < 139
  · rw [colR, trans_getD 0 139 certR i m hi (by rw [certR_length]; exact hm), rI]
  · rw [List.getD_eq_default _ _ (by rw [colR_length hi]; omega), rI,
      List.getD_eq_default certR [] (by rw [certR_length]; omega)]
    simp

theorem facL_length : facL.length = 141 := by simp [facL]

theorem xL_length {i : ℕ} (hi : i < 139) : (xL i).length = 141 := by
  simp [xL, facL_length, sd_length, colR_length hi]

theorem rZ_eq (m : ℤ) (i : ℕ) : rZ m i = if 0 ≤ m then rI m.toNat i else 0 := by
  unfold rZ
  by_cases h0 : 0 ≤ m
  · by_cases h1 : m < 139
    · simp [h0, h1]
    · rw [if_neg (by omega), if_pos h0, rI, List.getD_eq_default certR []
        (by rw [certR_length]; omega)]
      simp
  · simp [h0]

/-- The streamed column formula agrees with the three-point second difference. -/
theorem xI_eq {k i : ℕ} (hk : k < 141) (hi : i < 139) :
    xI k i = -(25 * (((k : ℤ) - 70) * ((k : ℤ) - 70)) * SI + C68) * wZ ((k : ℤ) - 70) i := by
  have hs : (sd (0 :: 0 :: (colR i ++ [0, 0]))).length = 141 := by
    simp [sd_length, colR_length hi]
  rw [xI, xL, getD_zipWith (by rw [facL_length]; exact hk) (by rw [hs]; exact hk),
    sd_getD _ _ (by simp [colR_length hi]; omega), pad_getD, pad_getD, pad_getD, facL,
    getD_map_range _ _ hk, wZ, rZ_eq, rZ_eq, rZ_eq]
  congr 1
  rcases Nat.lt_or_ge k 2 with h | h
  · interval_cases k <;> simp [colR_getD hi]
  · rw [if_pos (by omega), if_pos (by omega), if_pos h, if_pos (by omega), if_pos (by omega),
      if_pos (by omega), colR_getD hi, colR_getD hi, colR_getD hi]
    rw [show k + 1 - 2 = ((k : ℤ) - 70 + 69).toNat by omega,
      show k - 2 = ((k : ℤ) - 70 + 68).toNat by omega, show k + 2 - 2 = ((k : ℤ) - 70 + 70).toNat by omega]

theorem mkCol_eq (kp : List (ℕ × ℤ)) (fac d2l tkl drl trl c : List ℤ) (ad aT bt : ℕ) {α : Sort _}
    (k : Col → α) : mkCol kp fac d2l tkl drl trl c ad aT bt k = k (colOf kp fac d2l tkl drl trl c ad aT bt) := by
  simp only [mkCol, fL_eq, fN_eq, fI_eq, colOf]

theorem mkCols_eq (kp : List (ℕ × ℤ)) (fac d2l tkl drl trl : List ℤ) {α : Sort _} :
    ∀ (cs : List (List ℤ)) (as ts bs : List ℕ) (k : List Col → α),
      mkCols kp fac d2l tkl drl trl cs as ts bs k = k (colsOf kp fac d2l tkl drl trl cs as ts bs)
  | c :: cs, a :: as, t :: ts, b :: bs, k => by
      rw [mkCols, mkCol_eq, mkCols_eq kp fac d2l tkl drl trl cs as ts bs, colsOf]
  | [], _, _, _, k => by cases ‹List ℕ› <;> rfl
  | _ :: _, [], _, _, k => rfl
  | _ :: _, _ :: _, [], _, k => rfl
  | _ :: _, _ :: _, _ :: _, [], k => rfl

theorem colsOf_getD (kp : List (ℕ × ℤ)) (fac d2l tkl drl trl : List ℤ) :
    ∀ (cs : List (List ℤ)) (as ts bs : List ℕ) (i : ℕ), i < cs.length → i < as.length →
      i < ts.length → i < bs.length →
      (colsOf kp fac d2l tkl drl trl cs as ts bs).getD i default =
        colOf kp fac d2l tkl drl trl (cs.getD i []) (as.getD i 0) (ts.getD i 0) (bs.getD i 0)
  | c :: cs, a :: as, t :: ts, b :: bs, 0, _, _, _, _ => rfl
  | c :: cs, a :: as, t :: ts, b :: bs, i + 1, h1, h2, h3, h4 => by
      simp only [colsOf, List.getD_cons_succ]
      exact colsOf_getD kp fac d2l tkl drl trl cs as ts bs i (by simpa using h1) (by simpa using h2)
        (by simpa using h3) (by simpa using h4)
  | [], _, _, _, _, h, _, _, _ => absurd h (by simp)
  | _ :: _, [], _, _, _, _, h, _, _ => absurd h (by simp)
  | _ :: _, _ :: _, [], _, _, _, _, h, _ => absurd h (by simp)
  | _ :: _, _ :: _, _ :: _, [], _, _, _, _, h => absurd h (by simp)

theorem colsOf_length (kp : List (ℕ × ℤ)) (fac d2l tkl drl trl : List ℤ) :
    ∀ (cs : List (List ℤ)) (as ts bs : List ℕ) (n : ℕ), n ≤ cs.length → n ≤ as.length →
      n ≤ ts.length → n ≤ bs.length → n ≤ (colsOf kp fac d2l tkl drl trl cs as ts bs).length
  | c :: cs, a :: as, t :: ts, b :: bs, n, h1, h2, h3, h4 => by
      cases n with
      | zero => exact Nat.zero_le _
      | succ n =>
        simp only [colsOf, List.length_cons, Nat.succ_le_succ_iff]
        exact colsOf_length kp fac d2l tkl drl trl cs as ts bs n (by simpa using h1)
          (by simpa using h2) (by simpa using h3) (by simpa using h4)
  | [], _, _, _, n, h, _, _, _ => by simp at h; omega
  | _ :: _, [], _, _, n, _, h, _, _ => by simp at h; omega
  | _ :: _, _ :: _, [], _, n, _, _, h, _ => by simp at h; omega
  | _ :: _, _ :: _, _ :: _, [], n, _, _, _, h => by simp at h; omega

theorem rowOk_spec (de : ℤ) (ci : Col) (adi ati bti : ℕ) :
    ∀ (cs : List Col) (as ts bs : List ℕ) (Is1 Is2 : List Iv),
      rowOk de ci adi ati bti cs as ts bs Is1 Is2 = true →
      ∀ q, q < cs.length → q < as.length → q < ts.length → q < bs.length → q < Is1.length →
        q < Is2.length →
        ivOkD de (Is1.getD q ⟨0, 0⟩) (neF ci (cs.getD q default))
            ((adi : ℤ) * as.getD q 0 * T64 + CPI * ((ati : ℤ) * bs.getD q 0 + (ts.getD q 0 : ℤ) * bti) + RPI) = true ∧
        ivOkD de (Is2.getD q ⟨0, 0⟩) (neF ci (cs.getD q default))
            ((adi : ℤ) * as.getD q 0 * T64 + CPI * ((ati : ℤ) * bs.getD q 0 + (ts.getD q 0 : ℤ) * bti) + RPI) = true
  | cj :: cs, adj :: as, atj :: ts, btj :: bs, I1 :: Is1, I2 :: Is2, h, q, h1, h2, h3, h4, h5, h6 => by
      simp only [rowOk, fI_eq, Bool.and_eq_true] at h
      obtain ⟨⟨hA, hB⟩, hC⟩ := h
      cases q with
      | zero => exact ⟨hA, hB⟩
      | succ q =>
        simp only [List.getD_cons_succ]
        exact rowOk_spec de ci adi ati bti cs as ts bs Is1 Is2 hC q (by simpa using h1)
          (by simpa using h2) (by simpa using h3) (by simpa using h4) (by simpa using h5)
          (by simpa using h6)
  | [], _, _, _, _, _, _, q, h1, _, _, _, _, _ => absurd h1 (by simp)
  | _ :: _, [], _, _, _, _, _, q, _, h2, _, _, _, _ => absurd h2 (by simp)
  | _ :: _, _ :: _, [], _, _, _, _, q, _, _, h3, _, _, _ => absurd h3 (by simp)
  | _ :: _, _ :: _, _ :: _, [], _, _, _, q, _, _, _, h4, _, _ => absurd h4 (by simp)
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, _, q, _, _, _, _, h5, _ => absurd h5 (by simp)
  | _ :: _, _ :: _, _ :: _, _ :: _, _ :: _, [], _, q, _, _, _, _, _, h6 => absurd h6 (by simp)

theorem allOk_spec (de : ℤ) :
    ∀ (n i : ℕ) (cs : List Col) (as ts bs : List ℕ) (rs1 rs2 : List (List Iv)),
      allOk de i n cs as ts bs rs1 rs2 = true →
      ∀ p, p < n → (cs.getD p default).ok = true ∧
        rowOk de (cs.getD p default) (as.getD p 0) (ts.getD p 0) (bs.getD p 0) (cs.drop p)
          (as.drop p) (ts.drop p) (bs.drop p) ((rs1.getD p []).drop (i + p))
          ((rs2.getD p []).drop (i + p)) = true
  | 0, _, _, _, _, _, _, _, _, p, hp => absurd hp (Nat.not_lt_zero _)
  | n + 1, i, ci :: cs, adi :: as, ati :: ts, bti :: bs, r1 :: rs1, r2 :: rs2, h, p, hp => by
      simp only [allOk, Bool.and_eq_true] at h
      obtain ⟨⟨hA, hB⟩, hC⟩ := h
      cases p with
      | zero => exact ⟨hA, by simpa using hB⟩
      | succ p =>
        have := allOk_spec n (i + 1) cs as ts bs rs1 rs2 hC p (by omega)
        simp only [List.getD_cons_succ, List.drop_succ_cons]
        rw [show i + (p + 1) = i + 1 + p by omega]
        exact this
  | _ + 1, _, [], _, _, _, _, _, h, _, _ => by simp [allOk] at h
  | _ + 1, _, _ :: _, [], _, _, _, _, h, _, _ => by simp [allOk] at h
  | _ + 1, _, _ :: _, _ :: _, [], _, _, _, h, _, _ => by simp [allOk] at h
  | _ + 1, _, _ :: _, _ :: _, _ :: _, [], _, _, h, _, _ => by simp [allOk] at h
  | _ + 1, _, _ :: _, _ :: _, _ :: _, _ :: _, [], _, h, _, _ => by simp [allOk] at h
  | _ + 1, _, _ :: _, _ :: _, _ :: _, _ :: _, _ :: _, [], h, _, _ => by simp [allOk] at h
