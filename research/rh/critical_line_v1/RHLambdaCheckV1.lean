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

import RHExpEnclosureV1

/-!
# The integer checker for `Λ(1/2 + it)`

Complex intervals are pairs of `Iv`.  With `z = −3/4 + (t/2) i`, `a_j = (9/8)^j`:

* `ρ = (1 + 1/8)^z` by the binomial series (`binAux`) plus its remainder: no log, no cos, no sin;
* `P_j ∋ e^{−π a_j}` (`expNegPi`), `E_{m,j} = P_j^{m²}`;
* cell `(m, j)`: `ρ^j Σ_{k≤d} choose(z, k) a_j^{−k} I_k` (`cellAux`, the moments by their recursion),
  widened by `R_d I_0`;
* `lamIv` adds the three `m`, the tails beyond `X = (9/8)^J`, the three-term error, and `−1/(1/4 + t²)`.

`checkmirror.py` is the operation-for-operation mirror.  AUTHORITY_EFFECT = NONE.
-/

namespace AEGIS.RHLambdaCheckV1

open AEGIS.RHFixIntervalV1 AEGIS.RHExpEnclosureV1

variable (p : ℕ)

def isub (I J : Iv) : Iv := I.add J.neg

def iwiden (I : Iv) (e : ℤ) : Iv := ⟨I.lo - e, I.hi + e⟩

/-- A complex interval. -/
structure CIv where
  re : Iv
  im : Iv
  deriving DecidableEq, Repr

def cof (x y : ℚ) : CIv := ⟨ofQ p x, ofQ p y⟩

def cadd (C D : CIv) : CIv := ⟨C.re.add D.re, C.im.add D.im⟩

def cmul (C D : CIv) : CIv :=
  ⟨isub (C.re.mul p D.re) (C.im.mul p D.im), (C.re.mul p D.im).add (C.im.mul p D.re)⟩

def csmul (I : Iv) (C : CIv) : CIv := ⟨I.mul p C.re, I.mul p C.im⟩

def cwiden (C : CIv) (e : ℤ) : CIv := ⟨iwiden C.re e, iwiden C.im e⟩

/-- `(Σ_{i<k} choose(z, i) u^i, choose(z, k) u^k)`, `z = zr + zi i`. -/
def binAux (zr zi u : ℚ) : ℕ → CIv × CIv
  | 0 => (cof p 0 0, cof p 1 0)
  | k + 1 => match binAux zr zi u k with
    | (S, T) => (cadd S T, csmul p (ofQ p (u / (k + 1))) (cmul p T (cof p (zr - k) zi)))

/-- `(Σ_{i<k} T_i I_i, T_k, I_k)` with `T_k = choose(z, k) ainv^k` and the moment recursion
`I_{k+1} = ((k + 1) I_k − E_b h^{k+1}) / α`. -/
def cellAux (zr zi ainv h : ℚ) (invA Eb I0 : Iv) : ℕ → CIv × CIv × Iv
  | 0 => (cof p 0 0, cof p 1 0, I0)
  | k + 1 => match cellAux zr zi ainv h invA Eb I0 k with
    | (S, T, I) =>
      (cadd S (csmul p I T),
       csmul p (ofQ p (ainv / (k + 1))) (cmul p T (cof p (zr - k) zi)),
       (isub ((ofQ p (k + 1)).mul p I) (Eb.mul p (ofQ p (h ^ (k + 1))))).mul p invA)

/-- `[1/(π_hi m²), 1/(π_lo m²)]`. -/
def invAlpha (m : ℕ) : Iv := ⟨(ofQ p (1 / (piHi * m ^ 2))).lo, (ofQ p (1 / (piLo * m ^ 2))).hi⟩

/-- `β_k` in `ℚ`. -/
def betaQ (M : ℚ) : ℕ → ℚ
  | 0 => 1
  | k + 1 => betaQ M k * (M + k) / (k + 1)

/-- The binomial remainder `β_{d+1} U^{d+1} / (1 − U (M + d + 1)/(d + 2))`. -/
def remQ (M : ℚ) (d : ℕ) (U : ℚ) : ℚ := betaQ M (d + 1) * U ^ (d + 1) / (1 - U * (M + d + 1) / (d + 2))

/-- One cell `[a, 9a/8]` for `α = π m²`. -/
def cellV (zr zi : ℚ) (d : ℕ) (Rd : ℚ) (pw : CIv) (a : ℚ) (P P' : Iv) (m : ℕ) : CIv :=
  match (isub (powIv p P (m ^ 2)) (powIv p P' (m ^ 2))).mul p (invAlpha p m) with
  | I0 => cwiden (cmul p pw (cellAux p zr zi a⁻¹ (a / 8) (invAlpha p m) (powIv p P' (m ^ 2)) I0 (d + 1)).1)
      ⌈Rd * I0.hi⌉

/-- `(S₁, S₂, S₃, ρ^j, P_j)` after `j` cells. -/
def loopJ (zr zi : ℚ) (d s N : ℕ) (Rd : ℚ) (ρ : CIv) : ℕ → CIv × CIv × CIv × CIv × Iv
  | 0 => (cof p 0 0, cof p 0 0, cof p 0 0, cof p 1 0, expNegPi p 1 s N)
  | j + 1 => match loopJ zr zi d s N Rd ρ j with
    | (S1, S2, S3, pw, P) =>
      match expNegPi p ((9 / 8 : ℚ) ^ (j + 1)) s N with
      | P' => (cadd S1 (cellV p zr zi d Rd pw ((9 / 8 : ℚ) ^ j) P P' 1),
               cadd S2 (cellV p zr zi d Rd pw ((9 / 8 : ℚ) ^ j) P P' 2),
               cadd S3 (cellV p zr zi d Rd pw ((9 / 8 : ℚ) ^ j) P P' 3),
               cmul p pw ρ, P')

/-- `ρ = (9/8)^z`: the binomial sum plus its remainder. -/
def rhoIv (t M : ℚ) (K : ℕ) : CIv :=
  cwiden (binAux p (-3 / 4) (t / 2) (1 / 8) (K + 1)).1 ⌈remQ M K (1 / 8) * 2 ^ p⌉

/-- Twice the three tails beyond `X` plus the three-term error, in units of `2^{-p}`. -/
def tailW (PJ P0 : Iv) : ℤ :=
  2 * (⌈((powIv p PJ (1 ^ 2)).hi * (invAlpha p 1).hi : ℚ) / 2 ^ p⌉ +
       ⌈((powIv p PJ (2 ^ 2)).hi * (invAlpha p 2).hi : ℚ) / 2 ^ p⌉ +
       ⌈((powIv p PJ (3 ^ 2)).hi * (invAlpha p 3).hi : ℚ) / 2 ^ p⌉) +
    ⌈(P0.hi : ℚ) ^ 16 / 2 ^ (15 * p)⌉

/-- `2 re(S₁ + S₂ + S₃) ± W − 1/(1/4 + t²)`. -/
def lamCore (t : ℚ) (P0 : Iv) : CIv × CIv × CIv × CIv × Iv → Iv
  | (S1, S2, S3, _, PJ) =>
    isub (iwiden ((ofQ p 2).mul p (cadd (cadd S1 S2) S3).re) (tailW p PJ P0))
      (ofQ p (1 / (1 / 4 + t ^ 2)))

/-- The enclosure of `re Λ(1/2 + it)`. -/
def lamIv (t M : ℚ) (d K J s N : ℕ) : Iv :=
  lamCore p t (expNegPi p 1 s N)
    (loopJ p (-3 / 4) (t / 2) d s N (remQ M d (1 / 8)) (rhoIv p t M K) J)

end AEGIS.RHLambdaCheckV1
