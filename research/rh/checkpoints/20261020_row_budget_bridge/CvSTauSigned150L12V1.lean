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
/- Actual source tau boxes on all signed rows -150..150, at arbitrary precision. -/
import CvSTauR1PrimeL12V1
import CvSOddSignedEnclosureV1
import CvSRationalIntervalV1

namespace AEGIS.CvSTauSigned150L12V1
open AEGIS.CvSRowTailV1 AEGIS.CvSTauPrimeL12V1 AEGIS.CvSTauR1PrimeL12V1
open AEGIS.CvSRationalIntervalV1

def positiveLo (k : ℕ) : ℚ :=
  if k ≤ 70 then tauFLo.getD (k - 1) 0 else tauFLoExtra.getD (k - 71) 0

def positiveHi (k : ℕ) : ℚ :=
  if k ≤ 70 then tauFHi.getD (k - 1) 0 else tauFHiExtra.getD (k - 71) 0

theorem positive_mem {M : ℕ} (hM : 3 ≤ M) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 150) :
    (positiveLo k : ℝ) ≤ tau M (6 / 5) k ∧ tau M (6 / 5) k ≤ (positiveHi k : ℝ) := by
  by_cases h : k ≤ 70
  · simpa only [positiveLo, positiveHi, if_pos h] using tau_mem hM hk1 h
  · simpa only [positiveLo, positiveHi, if_neg h] using tau_mem_R1 hM (by omega) hk

def signedLo (k : ℤ) : ℚ :=
  if k < 0 then -positiveHi k.natAbs else if k = 0 then 0 else positiveLo k.natAbs

def signedHi (k : ℤ) : ℚ :=
  if k < 0 then -positiveLo k.natAbs else if k = 0 then 0 else positiveHi k.natAbs

/-- Actual source enclosures, including negative rows and the exact zero row. -/
theorem signed_tau_bounds {M : ℕ} (hM : 3 ≤ M) (k : ℤ) (hk : k.natAbs ≤ 150) :
    (signedLo k : ℝ) ≤ tau M (6 / 5) k ∧ tau M (6 / 5) k ≤ (signedHi k : ℝ) := by
  have h := AEGIS.CvSOddSignedEnclosureV1.signed_rational_bounds (tau M (6 / 5))
    positiveLo positiveHi 150 (tau_zero M (6 / 5)) (tau_neg M (6 / 5))
    (fun n hn1 hn => positive_mem hM hn1 hn) k hk
  simpa only [signedLo, signedHi] using h

/-- Outward fixed-point tau boxes at every p, from the actual analytic source. -/
theorem signed_tau_interval (p : ℕ) {M : ℕ} (hM : 3 ≤ M) (k : ℤ)
    (hk : k.natAbs ≤ 150) :
    (rationalRange p (signedLo k) (signedHi k)).Mem p (tau M (6 / 5) k) :=
  rationalRange_mem p _ _ (signed_tau_bounds hM k hk).1 (signed_tau_bounds hM k hk).2

end AEGIS.CvSTauSigned150L12V1
#print axioms AEGIS.CvSTauSigned150L12V1.positive_mem
#print axioms AEGIS.CvSTauSigned150L12V1.signed_tau_bounds
#print axioms AEGIS.CvSTauSigned150L12V1.signed_tau_interval
