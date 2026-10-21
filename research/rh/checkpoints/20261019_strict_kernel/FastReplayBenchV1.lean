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
import CvSProjectedEntryL12V1
open AEGIS.CvSPackedGramV1 AEGIS.RHFixIntervalV1 AEGIS.CvSProjectedPackedCertificateL12V1
namespace AEGIS.FastTestV1
open AEGIS.CvSProjectedEntryL12V1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
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
def trans {α : Type} (d : α) : ℕ → List (List α) → List (List α)
  | 0, _ => []
  | n + 1, rows => rows.map (fun r => r.headD d) :: trans d n (rows.map List.tail)
def sd : List ℤ → List ℤ
  | a :: b :: c :: t => (2 * b - a - c) :: sd (b :: c :: t)
  | _ => []
def facL : List ℤ := (List.range 141).map fun k => -(25 * (((k : ℤ) - 70) * ((k : ℤ) - 70)) * SI + C68)
def d2L : List ℤ := (List.range 141).map d2
def tKL : List ℤ := (List.range 141).map tK
def drL : List ℤ := (List.range 141).map dr
def trL : List ℤ := (List.range 141).map tr
def ldot (a b : List ℤ) : ℤ := (List.zipWith (· * ·) a b).sum
def B3 : ℕ := 2 ^ 168
def b3 : ℕ := 2 ^ 353
def B4 : ℕ := 2 ^ 321
def b4 : ℕ := 2 ^ 661

structure Col where
  ok : Bool
  pA : ℕ
  sA : ℤ
  pX : ℕ
  sX : ℤ
  pU : ℕ
  sU : ℤ
  pW : ℕ
  sW : ℤ

structure Ctx where
  kp : List (ℕ × ℤ)
  fac : List ℤ
  d2l : List ℤ
  tkl : List ℤ
  drl : List ℤ
  trl : List ℤ

def mkCol (C : Ctx) (c : List ℤ) (ad aT bt : ℕ) {α : Sort _} (k : Col → α) : α :=
  fL (List.zipWith (· * ·) C.fac (sd (0 :: 0 :: c ++ [0, 0]))) fun x =>
  fN (pack b1 (offRow B1 x).reverse) fun R => fI x.sum fun t =>
  fL (C.kp.map fun p => gramEntry b1 B1 141 p.1 p.2 R t) fun h =>
  fL (List.zipWith (· * ·) C.d2l x) fun a =>
  fL (List.zipWith (· * ·) C.tkl x) fun tx =>
  fN (pack b3 (offRow B3 a)) fun pA => fI a.sum fun sA =>
  fN (pack b3 (offRow B3 x).reverse) fun pX =>
  fN (pack b4 (offRow B4 (tx ++ h))) fun pU => fI (tx ++ h).sum fun sU =>
  fN (pack b4 (offRow B4 (h ++ tx)).reverse) fun pW =>
  k { ok := x.all (fun v => v.natAbs ≤ XMI) && h.all (fun v => v.natAbs ≤ HMI) &&
        a.all (fun v => v.natAbs ≤ B3) && tx.all (fun v => v.natAbs ≤ B3) &&
        decide (T128 * ldot C.drl (List.zipWith (· * ·) x x) ≤ (ad : ℤ) * ad * Q49) &&
        decide (T128 * ldot C.trl (List.zipWith (· * ·) x x) ≤ (aT : ℤ) * aT * Q49) &&
        decide (T128 * ldot C.trl (List.zipWith (· * ·) h h) ≤ (bt : ℤ) * bt * (Q49 * LAM * LAM))
      pA := pA, sA := sA, pX := pX, sX := t, pU := pU, sU := sU, pW := pW, sW := sU }

def mkCols (C : Ctx) {α : Sort _} : List (List ℤ) → List ℕ → List ℕ → List ℕ → (List Col → α) → α
  | c :: cs, a :: as, t :: ts, b :: bs, k => mkCol C c a t b fun col => mkCols C cs as ts bs fun l => k (col :: l)
  | _, _, _, _, k => k []

def neF (ci cj : Col) : ℤ :=
  C1 * gramEntry b3 B3 141 ci.pA ci.sA cj.pX cj.sX + C2 * gramEntry b4 B4 282 ci.pU ci.sU cj.pW cj.sW

def ivOkD (de : ℤ) (I : Iv) (ne r : ℤ) : Bool :=
  decide (I.lo * SR * de + r * T64 * de ≤ ne * T64 * SR) &&
    decide (ne * T64 * SR + r * T64 * de ≤ I.hi * SR * de)

def rowOk (de : ℤ) (ci : Col) (adi ati bti : ℕ) : List Col → List ℕ → List ℕ → List ℕ → List Iv → List Iv → Bool
  | cj :: cs, adj :: as, atj :: ts, btj :: bs, I1 :: Is1, I2 :: Is2 =>
      fI (neF ci cj) fun ne =>
      let r := (adi : ℤ) * adj * T64 + CPI * ((ati : ℤ) * btj + (atj : ℤ) * bti) + RPI
      ivOkD de I1 ne r && ivOkD de I2 ne r && rowOk de ci adi ati bti cs as ts bs Is1 Is2
  | _, _, _, _, _, _ => true

def allOk (de : ℤ) : ℕ → List Col → List ℕ → List ℕ → List ℕ → List (List Iv) → List (List Iv) → Bool
  | 0, _, _, _, _, _, _ => true
  | n + 1, ci :: cs, adi :: as, ati :: ts, bti :: bs, r1 :: rs1, r2 :: rs2 =>
      ci.ok && rowOk de ci adi ati bti (ci :: cs) (adi :: as) (ati :: ts) (bti :: bs)
        (r1.drop (139 - (n + 1))) (r2.drop (139 - (n + 1))) &&
      allOk de n cs as ts bs rs1 rs2
  | _ + 1, _, _, _, _, _, _ => false

def top : Bool :=
  fP kPk fun kp => fL facL fun fac => fL d2L fun d2l => fL tKL fun tkl => fL drL fun drl =>
  fL trL fun trl => fI DE fun de =>
  mkCols ⟨kp, fac, d2l, tkl, drl, trl⟩ (trans 0 139 certR) AD AT BT fun cols =>
  allOk de 139 cols AD AT BT certI (trans ⟨0, 0⟩ 139 certI)

set_option profiler true
theorem t : top = true := by decide +kernel
end AEGIS.FastTestV1
