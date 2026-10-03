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

import AEGISOverlay.RHKreinSplineSupportV1

/-!
# Exact coefficient and symbol declarations, isolated from the Weil criterion

The four declarations below are moved byte-identically from the PR #51
RHKreinExplicitCorrectionV1 source. No coefficient, center, scale or parity
convention is changed. The namespace remains the original one.
-/

open Set MeasureTheory Complex FourierTransform
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinExplicitCorrectionV1

/-- Exact rational hat coefficients in increasing center order. -/
def hatCoefficient : Fin 199 → ℚ :=
  ![-100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -190093321285891/2500000000,
    100000,
    100000,
    100000,
    100000,
    29666418987513/2500000000,
    -100000,
    -100000,
    -100000,
    -117731535372369/2500000000,
    100000,
    100000,
    100000,
    100000,
    100000,
    100000,
    50425751969473/2000000000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    515177348963881/10000000000,
    100000,
    100000,
    100000,
    100000,
    100000,
    100000,
    -100000,
    -100000,
    100000,
    100000,
    100000,
    -51422462806047/1000000000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -116660983646653/1250000000,
    100000,
    100000,
    100000,
    100000,
    100000,
    100000,
    100000,
    -166526644754763/10000000000,
    -100000,
    -100000,
    -100000,
    -100000,
    -118048813499739/1250000000,
    100000,
    100000,
    100000,
    100000,
    100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    2953816304371/1000000000,
    100000,
    100000,
    100000,
    100000,
    100000,
    100000,
    7920263226739/1000000000,
    -100000,
    -100000,
    -100000,
    -100000,
    -164690278619151/10000000000,
    100000,
    100000,
    100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    6934524025071/80000000,
    100000,
    100000,
    100000,
    100000,
    100000,
    730856184163993/10000000000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    414340348739593/10000000000,
    100000,
    100000,
    100000,
    100000,
    378057512105339/10000000000,
    -100000,
    -100000,
    -100000,
    -618999438984917/10000000000,
    100000,
    100000,
    -100000,
    -100000,
    -101839738853771/2500000000,
    100000,
    100000,
    100000,
    100000,
    86995914959651/1000000000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    100000,
    100000,
    -25574621798421/400000000,
    -100000,
    -469702038657277/10000000000,
    100000,
    100000,
    100000,
    100000,
    100000,
    -247976924265647/5000000000,
    -100000,
    -100000,
    -100000,
    -100000,
    -100000,
    296561423630109/10000000000,
    100000,
    100000,
    100000,
    100000,
    100000,
    -373908230082811/5000000000,
    -100000,
    -100000,
    -100000,
    -100000,
    -186287944404417/10000000000,
    100000,
    100000,
    100000,
    100000,
    -16872084697291/5000000000,
    -100000,
    -100000,
    -100000,
    200108515493551/10000000000,
    100000,
    100000,
    100000,
    -100000,
    -100000,
    -100000,
    -100000,
    730445128203157/10000000000,
    100000,
    100000,
    19841790224691/2000000000,
    -47556077772879/5000000000,
    100000,
    -886028847662807/10000000000,
    -100000,
    -100000,
    110857698784947/10000000000,
    100000,
    100000,
    -431069777588841/5000000000]

/-- Exact rational derivative coefficients in derivative order zero through four. -/
def splineCoefficient : Fin 5 → ℚ :=
  ![234102120892757/5000000000,
    -12240399939171/2500000000,
    -2918648959121/10000000000,
    123578990441/10000000000,
    9711997751/10000000000]

def hatCenter (j : Fin 199) : ℝ := ((j.val : ℝ) + 41) / 50

/-- The explicit angular Fourier correction used by the exact certificate. -/
def correctionSymbol (t : ℝ) : ℝ :=
  (2 / 50) * Real.sinc (t / 100) ^ 2 *
    (∑ j : Fin 199, (hatCoefficient j : ℝ) * Real.cos (t * hatCenter j)) +
  Real.sinc (t / 2000) ^ 19 *
    (∑ j : Fin 5, (splineCoefficient j : ℝ) * t ^ j.val *
      (if j.val % 2 = 0 then Real.cos (t * (1619 / 2000))
       else Real.sin (t * (1619 / 2000))))

/-- The extracted center is the same rational grid expression. -/
theorem hatCenter_formula (j : Fin 199) :
    hatCenter j = ((j.val : ℝ) + 41) / 50 := rfl

end AEGIS.RHKreinExplicitCorrectionV1

#print axioms AEGIS.RHKreinExplicitCorrectionV1.hatCenter_formula
