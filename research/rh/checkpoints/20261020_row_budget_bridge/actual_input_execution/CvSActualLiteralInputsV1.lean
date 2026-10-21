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
/- Actual-source input integration candidate. Requires original-import kernel replay. -/
import CvSActualRowInputL12V1
import CvSProjectedSymmetryV1
import CvSSourceProductAllV1
import CvSSourceQAllV1
import CvSFullBudgetJoinV1
import CvSAnalyticERows0
import CvSAnalyticERows1
import CvSAnalyticERows2
import CvSAnalyticERows3
import CvSAnalyticERows4
import CvSAnalyticERows5
import CvSAnalyticERows6
import CvSAnalyticERows7
import CvSAnalyticERows8
import CvSAnalyticERows9
import CvSAnalyticERows10
import CvSAnalyticERows11
import CvSAnalyticERows12
import CvSAnalyticERows13
import CvSAnalyticERows14
import CvSAnalyticERows15
import CvSAnalyticERows16
import CvSAnalyticERows17
import CvSAnalyticERows18
import CvSAnalyticERows19
import CvSAnalyticERows20
import CvSAnalyticERows21
import CvSAnalyticERows22
import CvSAnalyticERows23
import CvSAnalyticERows24
import CvSAnalyticERows25
import CvSAnalyticERows26
import CvSAnalyticERows27
import CvSAnalyticERows28
import CvSAnalyticERows29
import CvSAnalyticERows30
import CvSAnalyticXColumns0
import CvSAnalyticXColumns1
import CvSAnalyticXColumns2
import CvSAnalyticXColumns3
import CvSAnalyticXColumns4
import CvSAnalyticXColumns5
import CvSAnalyticXColumns6
import CvSAnalyticXColumns7
import CvSAnalyticXColumns8
import CvSAnalyticXColumns9
import CvSAnalyticXColumns10
import CvSAnalyticXColumns11
import CvSAnalyticXColumns12
import CvSAnalyticXColumns13
import CvSAnalyticGRows0
import CvSAnalyticGRows1
import CvSAnalyticGRows2
import CvSAnalyticGRows3
import CvSAnalyticGRows4
import CvSAnalyticGRows5
import CvSAnalyticGRows6
import CvSAnalyticGRows7
import CvSAnalyticGRows8
import CvSAnalyticGRows9
import CvSAnalyticGRows10
import CvSAnalyticGRows11
import CvSAnalyticGRows12
import CvSAnalyticGRows13
import CvSAnalyticGRows14
import CvSAnalyticScalarInputsV1
import Mathlib.Tactic.FinCases
open scoped BigOperators ComplexConjugate
namespace AEGIS.CvSActualLiteralInputsV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSIntervalMatrixProductV1
open AEGIS.CvSActualRowInputL12V1 AEGIS.CvSSourceProductAllV1
open AEGIS.CvSProjectedPackedCertificateL12V1 AEGIS.CvSListIntervalDotV1
open AEGIS.CvSCachedColumnV1 AEGIS.CvSSourceQNormalizeV1
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem E_source (r : Fin 301) (k : Fin 141) :
    (eRow r).values.getD k.val ⟨0, 0⟩ = kernelBox 96 (rowIndex r) k := by
  fin_cases r
  · exact AEGIS.CvSAnalyticERows0.row0 k
  · exact AEGIS.CvSAnalyticERows0.row1 k
  · exact AEGIS.CvSAnalyticERows0.row2 k
  · exact AEGIS.CvSAnalyticERows0.row3 k
  · exact AEGIS.CvSAnalyticERows0.row4 k
  · exact AEGIS.CvSAnalyticERows0.row5 k
  · exact AEGIS.CvSAnalyticERows0.row6 k
  · exact AEGIS.CvSAnalyticERows0.row7 k
  · exact AEGIS.CvSAnalyticERows0.row8 k
  · exact AEGIS.CvSAnalyticERows0.row9 k
  · exact AEGIS.CvSAnalyticERows1.row10 k
  · exact AEGIS.CvSAnalyticERows1.row11 k
  · exact AEGIS.CvSAnalyticERows1.row12 k
  · exact AEGIS.CvSAnalyticERows1.row13 k
  · exact AEGIS.CvSAnalyticERows1.row14 k
  · exact AEGIS.CvSAnalyticERows1.row15 k
  · exact AEGIS.CvSAnalyticERows1.row16 k
  · exact AEGIS.CvSAnalyticERows1.row17 k
  · exact AEGIS.CvSAnalyticERows1.row18 k
  · exact AEGIS.CvSAnalyticERows1.row19 k
  · exact AEGIS.CvSAnalyticERows2.row20 k
  · exact AEGIS.CvSAnalyticERows2.row21 k
  · exact AEGIS.CvSAnalyticERows2.row22 k
  · exact AEGIS.CvSAnalyticERows2.row23 k
  · exact AEGIS.CvSAnalyticERows2.row24 k
  · exact AEGIS.CvSAnalyticERows2.row25 k
  · exact AEGIS.CvSAnalyticERows2.row26 k
  · exact AEGIS.CvSAnalyticERows2.row27 k
  · exact AEGIS.CvSAnalyticERows2.row28 k
  · exact AEGIS.CvSAnalyticERows2.row29 k
  · exact AEGIS.CvSAnalyticERows3.row30 k
  · exact AEGIS.CvSAnalyticERows3.row31 k
  · exact AEGIS.CvSAnalyticERows3.row32 k
  · exact AEGIS.CvSAnalyticERows3.row33 k
  · exact AEGIS.CvSAnalyticERows3.row34 k
  · exact AEGIS.CvSAnalyticERows3.row35 k
  · exact AEGIS.CvSAnalyticERows3.row36 k
  · exact AEGIS.CvSAnalyticERows3.row37 k
  · exact AEGIS.CvSAnalyticERows3.row38 k
  · exact AEGIS.CvSAnalyticERows3.row39 k
  · exact AEGIS.CvSAnalyticERows4.row40 k
  · exact AEGIS.CvSAnalyticERows4.row41 k
  · exact AEGIS.CvSAnalyticERows4.row42 k
  · exact AEGIS.CvSAnalyticERows4.row43 k
  · exact AEGIS.CvSAnalyticERows4.row44 k
  · exact AEGIS.CvSAnalyticERows4.row45 k
  · exact AEGIS.CvSAnalyticERows4.row46 k
  · exact AEGIS.CvSAnalyticERows4.row47 k
  · exact AEGIS.CvSAnalyticERows4.row48 k
  · exact AEGIS.CvSAnalyticERows4.row49 k
  · exact AEGIS.CvSAnalyticERows5.row50 k
  · exact AEGIS.CvSAnalyticERows5.row51 k
  · exact AEGIS.CvSAnalyticERows5.row52 k
  · exact AEGIS.CvSAnalyticERows5.row53 k
  · exact AEGIS.CvSAnalyticERows5.row54 k
  · exact AEGIS.CvSAnalyticERows5.row55 k
  · exact AEGIS.CvSAnalyticERows5.row56 k
  · exact AEGIS.CvSAnalyticERows5.row57 k
  · exact AEGIS.CvSAnalyticERows5.row58 k
  · exact AEGIS.CvSAnalyticERows5.row59 k
  · exact AEGIS.CvSAnalyticERows6.row60 k
  · exact AEGIS.CvSAnalyticERows6.row61 k
  · exact AEGIS.CvSAnalyticERows6.row62 k
  · exact AEGIS.CvSAnalyticERows6.row63 k
  · exact AEGIS.CvSAnalyticERows6.row64 k
  · exact AEGIS.CvSAnalyticERows6.row65 k
  · exact AEGIS.CvSAnalyticERows6.row66 k
  · exact AEGIS.CvSAnalyticERows6.row67 k
  · exact AEGIS.CvSAnalyticERows6.row68 k
  · exact AEGIS.CvSAnalyticERows6.row69 k
  · exact AEGIS.CvSAnalyticERows7.row70 k
  · exact AEGIS.CvSAnalyticERows7.row71 k
  · exact AEGIS.CvSAnalyticERows7.row72 k
  · exact AEGIS.CvSAnalyticERows7.row73 k
  · exact AEGIS.CvSAnalyticERows7.row74 k
  · exact AEGIS.CvSAnalyticERows7.row75 k
  · exact AEGIS.CvSAnalyticERows7.row76 k
  · exact AEGIS.CvSAnalyticERows7.row77 k
  · exact AEGIS.CvSAnalyticERows7.row78 k
  · exact AEGIS.CvSAnalyticERows7.row79 k
  · exact AEGIS.CvSAnalyticERows8.row80 k
  · exact AEGIS.CvSAnalyticERows8.row81 k
  · exact AEGIS.CvSAnalyticERows8.row82 k
  · exact AEGIS.CvSAnalyticERows8.row83 k
  · exact AEGIS.CvSAnalyticERows8.row84 k
  · exact AEGIS.CvSAnalyticERows8.row85 k
  · exact AEGIS.CvSAnalyticERows8.row86 k
  · exact AEGIS.CvSAnalyticERows8.row87 k
  · exact AEGIS.CvSAnalyticERows8.row88 k
  · exact AEGIS.CvSAnalyticERows8.row89 k
  · exact AEGIS.CvSAnalyticERows9.row90 k
  · exact AEGIS.CvSAnalyticERows9.row91 k
  · exact AEGIS.CvSAnalyticERows9.row92 k
  · exact AEGIS.CvSAnalyticERows9.row93 k
  · exact AEGIS.CvSAnalyticERows9.row94 k
  · exact AEGIS.CvSAnalyticERows9.row95 k
  · exact AEGIS.CvSAnalyticERows9.row96 k
  · exact AEGIS.CvSAnalyticERows9.row97 k
  · exact AEGIS.CvSAnalyticERows9.row98 k
  · exact AEGIS.CvSAnalyticERows9.row99 k
  · exact AEGIS.CvSAnalyticERows10.row100 k
  · exact AEGIS.CvSAnalyticERows10.row101 k
  · exact AEGIS.CvSAnalyticERows10.row102 k
  · exact AEGIS.CvSAnalyticERows10.row103 k
  · exact AEGIS.CvSAnalyticERows10.row104 k
  · exact AEGIS.CvSAnalyticERows10.row105 k
  · exact AEGIS.CvSAnalyticERows10.row106 k
  · exact AEGIS.CvSAnalyticERows10.row107 k
  · exact AEGIS.CvSAnalyticERows10.row108 k
  · exact AEGIS.CvSAnalyticERows10.row109 k
  · exact AEGIS.CvSAnalyticERows11.row110 k
  · exact AEGIS.CvSAnalyticERows11.row111 k
  · exact AEGIS.CvSAnalyticERows11.row112 k
  · exact AEGIS.CvSAnalyticERows11.row113 k
  · exact AEGIS.CvSAnalyticERows11.row114 k
  · exact AEGIS.CvSAnalyticERows11.row115 k
  · exact AEGIS.CvSAnalyticERows11.row116 k
  · exact AEGIS.CvSAnalyticERows11.row117 k
  · exact AEGIS.CvSAnalyticERows11.row118 k
  · exact AEGIS.CvSAnalyticERows11.row119 k
  · exact AEGIS.CvSAnalyticERows12.row120 k
  · exact AEGIS.CvSAnalyticERows12.row121 k
  · exact AEGIS.CvSAnalyticERows12.row122 k
  · exact AEGIS.CvSAnalyticERows12.row123 k
  · exact AEGIS.CvSAnalyticERows12.row124 k
  · exact AEGIS.CvSAnalyticERows12.row125 k
  · exact AEGIS.CvSAnalyticERows12.row126 k
  · exact AEGIS.CvSAnalyticERows12.row127 k
  · exact AEGIS.CvSAnalyticERows12.row128 k
  · exact AEGIS.CvSAnalyticERows12.row129 k
  · exact AEGIS.CvSAnalyticERows13.row130 k
  · exact AEGIS.CvSAnalyticERows13.row131 k
  · exact AEGIS.CvSAnalyticERows13.row132 k
  · exact AEGIS.CvSAnalyticERows13.row133 k
  · exact AEGIS.CvSAnalyticERows13.row134 k
  · exact AEGIS.CvSAnalyticERows13.row135 k
  · exact AEGIS.CvSAnalyticERows13.row136 k
  · exact AEGIS.CvSAnalyticERows13.row137 k
  · exact AEGIS.CvSAnalyticERows13.row138 k
  · exact AEGIS.CvSAnalyticERows13.row139 k
  · exact AEGIS.CvSAnalyticERows14.row140 k
  · exact AEGIS.CvSAnalyticERows14.row141 k
  · exact AEGIS.CvSAnalyticERows14.row142 k
  · exact AEGIS.CvSAnalyticERows14.row143 k
  · exact AEGIS.CvSAnalyticERows14.row144 k
  · exact AEGIS.CvSAnalyticERows14.row145 k
  · exact AEGIS.CvSAnalyticERows14.row146 k
  · exact AEGIS.CvSAnalyticERows14.row147 k
  · exact AEGIS.CvSAnalyticERows14.row148 k
  · exact AEGIS.CvSAnalyticERows14.row149 k
  · exact AEGIS.CvSAnalyticERows15.row150 k
  · exact AEGIS.CvSAnalyticERows15.row151 k
  · exact AEGIS.CvSAnalyticERows15.row152 k
  · exact AEGIS.CvSAnalyticERows15.row153 k
  · exact AEGIS.CvSAnalyticERows15.row154 k
  · exact AEGIS.CvSAnalyticERows15.row155 k
  · exact AEGIS.CvSAnalyticERows15.row156 k
  · exact AEGIS.CvSAnalyticERows15.row157 k
  · exact AEGIS.CvSAnalyticERows15.row158 k
  · exact AEGIS.CvSAnalyticERows15.row159 k
  · exact AEGIS.CvSAnalyticERows16.row160 k
  · exact AEGIS.CvSAnalyticERows16.row161 k
  · exact AEGIS.CvSAnalyticERows16.row162 k
  · exact AEGIS.CvSAnalyticERows16.row163 k
  · exact AEGIS.CvSAnalyticERows16.row164 k
  · exact AEGIS.CvSAnalyticERows16.row165 k
  · exact AEGIS.CvSAnalyticERows16.row166 k
  · exact AEGIS.CvSAnalyticERows16.row167 k
  · exact AEGIS.CvSAnalyticERows16.row168 k
  · exact AEGIS.CvSAnalyticERows16.row169 k
  · exact AEGIS.CvSAnalyticERows17.row170 k
  · exact AEGIS.CvSAnalyticERows17.row171 k
  · exact AEGIS.CvSAnalyticERows17.row172 k
  · exact AEGIS.CvSAnalyticERows17.row173 k
  · exact AEGIS.CvSAnalyticERows17.row174 k
  · exact AEGIS.CvSAnalyticERows17.row175 k
  · exact AEGIS.CvSAnalyticERows17.row176 k
  · exact AEGIS.CvSAnalyticERows17.row177 k
  · exact AEGIS.CvSAnalyticERows17.row178 k
  · exact AEGIS.CvSAnalyticERows17.row179 k
  · exact AEGIS.CvSAnalyticERows18.row180 k
  · exact AEGIS.CvSAnalyticERows18.row181 k
  · exact AEGIS.CvSAnalyticERows18.row182 k
  · exact AEGIS.CvSAnalyticERows18.row183 k
  · exact AEGIS.CvSAnalyticERows18.row184 k
  · exact AEGIS.CvSAnalyticERows18.row185 k
  · exact AEGIS.CvSAnalyticERows18.row186 k
  · exact AEGIS.CvSAnalyticERows18.row187 k
  · exact AEGIS.CvSAnalyticERows18.row188 k
  · exact AEGIS.CvSAnalyticERows18.row189 k
  · exact AEGIS.CvSAnalyticERows19.row190 k
  · exact AEGIS.CvSAnalyticERows19.row191 k
  · exact AEGIS.CvSAnalyticERows19.row192 k
  · exact AEGIS.CvSAnalyticERows19.row193 k
  · exact AEGIS.CvSAnalyticERows19.row194 k
  · exact AEGIS.CvSAnalyticERows19.row195 k
  · exact AEGIS.CvSAnalyticERows19.row196 k
  · exact AEGIS.CvSAnalyticERows19.row197 k
  · exact AEGIS.CvSAnalyticERows19.row198 k
  · exact AEGIS.CvSAnalyticERows19.row199 k
  · exact AEGIS.CvSAnalyticERows20.row200 k
  · exact AEGIS.CvSAnalyticERows20.row201 k
  · exact AEGIS.CvSAnalyticERows20.row202 k
  · exact AEGIS.CvSAnalyticERows20.row203 k
  · exact AEGIS.CvSAnalyticERows20.row204 k
  · exact AEGIS.CvSAnalyticERows20.row205 k
  · exact AEGIS.CvSAnalyticERows20.row206 k
  · exact AEGIS.CvSAnalyticERows20.row207 k
  · exact AEGIS.CvSAnalyticERows20.row208 k
  · exact AEGIS.CvSAnalyticERows20.row209 k
  · exact AEGIS.CvSAnalyticERows21.row210 k
  · exact AEGIS.CvSAnalyticERows21.row211 k
  · exact AEGIS.CvSAnalyticERows21.row212 k
  · exact AEGIS.CvSAnalyticERows21.row213 k
  · exact AEGIS.CvSAnalyticERows21.row214 k
  · exact AEGIS.CvSAnalyticERows21.row215 k
  · exact AEGIS.CvSAnalyticERows21.row216 k
  · exact AEGIS.CvSAnalyticERows21.row217 k
  · exact AEGIS.CvSAnalyticERows21.row218 k
  · exact AEGIS.CvSAnalyticERows21.row219 k
  · exact AEGIS.CvSAnalyticERows22.row220 k
  · exact AEGIS.CvSAnalyticERows22.row221 k
  · exact AEGIS.CvSAnalyticERows22.row222 k
  · exact AEGIS.CvSAnalyticERows22.row223 k
  · exact AEGIS.CvSAnalyticERows22.row224 k
  · exact AEGIS.CvSAnalyticERows22.row225 k
  · exact AEGIS.CvSAnalyticERows22.row226 k
  · exact AEGIS.CvSAnalyticERows22.row227 k
  · exact AEGIS.CvSAnalyticERows22.row228 k
  · exact AEGIS.CvSAnalyticERows22.row229 k
  · exact AEGIS.CvSAnalyticERows23.row230 k
  · exact AEGIS.CvSAnalyticERows23.row231 k
  · exact AEGIS.CvSAnalyticERows23.row232 k
  · exact AEGIS.CvSAnalyticERows23.row233 k
  · exact AEGIS.CvSAnalyticERows23.row234 k
  · exact AEGIS.CvSAnalyticERows23.row235 k
  · exact AEGIS.CvSAnalyticERows23.row236 k
  · exact AEGIS.CvSAnalyticERows23.row237 k
  · exact AEGIS.CvSAnalyticERows23.row238 k
  · exact AEGIS.CvSAnalyticERows23.row239 k
  · exact AEGIS.CvSAnalyticERows24.row240 k
  · exact AEGIS.CvSAnalyticERows24.row241 k
  · exact AEGIS.CvSAnalyticERows24.row242 k
  · exact AEGIS.CvSAnalyticERows24.row243 k
  · exact AEGIS.CvSAnalyticERows24.row244 k
  · exact AEGIS.CvSAnalyticERows24.row245 k
  · exact AEGIS.CvSAnalyticERows24.row246 k
  · exact AEGIS.CvSAnalyticERows24.row247 k
  · exact AEGIS.CvSAnalyticERows24.row248 k
  · exact AEGIS.CvSAnalyticERows24.row249 k
  · exact AEGIS.CvSAnalyticERows25.row250 k
  · exact AEGIS.CvSAnalyticERows25.row251 k
  · exact AEGIS.CvSAnalyticERows25.row252 k
  · exact AEGIS.CvSAnalyticERows25.row253 k
  · exact AEGIS.CvSAnalyticERows25.row254 k
  · exact AEGIS.CvSAnalyticERows25.row255 k
  · exact AEGIS.CvSAnalyticERows25.row256 k
  · exact AEGIS.CvSAnalyticERows25.row257 k
  · exact AEGIS.CvSAnalyticERows25.row258 k
  · exact AEGIS.CvSAnalyticERows25.row259 k
  · exact AEGIS.CvSAnalyticERows26.row260 k
  · exact AEGIS.CvSAnalyticERows26.row261 k
  · exact AEGIS.CvSAnalyticERows26.row262 k
  · exact AEGIS.CvSAnalyticERows26.row263 k
  · exact AEGIS.CvSAnalyticERows26.row264 k
  · exact AEGIS.CvSAnalyticERows26.row265 k
  · exact AEGIS.CvSAnalyticERows26.row266 k
  · exact AEGIS.CvSAnalyticERows26.row267 k
  · exact AEGIS.CvSAnalyticERows26.row268 k
  · exact AEGIS.CvSAnalyticERows26.row269 k
  · exact AEGIS.CvSAnalyticERows27.row270 k
  · exact AEGIS.CvSAnalyticERows27.row271 k
  · exact AEGIS.CvSAnalyticERows27.row272 k
  · exact AEGIS.CvSAnalyticERows27.row273 k
  · exact AEGIS.CvSAnalyticERows27.row274 k
  · exact AEGIS.CvSAnalyticERows27.row275 k
  · exact AEGIS.CvSAnalyticERows27.row276 k
  · exact AEGIS.CvSAnalyticERows27.row277 k
  · exact AEGIS.CvSAnalyticERows27.row278 k
  · exact AEGIS.CvSAnalyticERows27.row279 k
  · exact AEGIS.CvSAnalyticERows28.row280 k
  · exact AEGIS.CvSAnalyticERows28.row281 k
  · exact AEGIS.CvSAnalyticERows28.row282 k
  · exact AEGIS.CvSAnalyticERows28.row283 k
  · exact AEGIS.CvSAnalyticERows28.row284 k
  · exact AEGIS.CvSAnalyticERows28.row285 k
  · exact AEGIS.CvSAnalyticERows28.row286 k
  · exact AEGIS.CvSAnalyticERows28.row287 k
  · exact AEGIS.CvSAnalyticERows28.row288 k
  · exact AEGIS.CvSAnalyticERows28.row289 k
  · exact AEGIS.CvSAnalyticERows29.row290 k
  · exact AEGIS.CvSAnalyticERows29.row291 k
  · exact AEGIS.CvSAnalyticERows29.row292 k
  · exact AEGIS.CvSAnalyticERows29.row293 k
  · exact AEGIS.CvSAnalyticERows29.row294 k
  · exact AEGIS.CvSAnalyticERows29.row295 k
  · exact AEGIS.CvSAnalyticERows29.row296 k
  · exact AEGIS.CvSAnalyticERows29.row297 k
  · exact AEGIS.CvSAnalyticERows29.row298 k
  · exact AEGIS.CvSAnalyticERows29.row299 k
  · exact AEGIS.CvSAnalyticERows30.row300 k
theorem X_source (k : Fin 141) (i : Fin 139) :
    (inputColumn i).x.values.getD k.val ⟨0, 0⟩ = xBox k i := by
  fin_cases i
  · exact AEGIS.CvSAnalyticXColumns0.column0 k
  · exact AEGIS.CvSAnalyticXColumns0.column1 k
  · exact AEGIS.CvSAnalyticXColumns0.column2 k
  · exact AEGIS.CvSAnalyticXColumns0.column3 k
  · exact AEGIS.CvSAnalyticXColumns0.column4 k
  · exact AEGIS.CvSAnalyticXColumns0.column5 k
  · exact AEGIS.CvSAnalyticXColumns0.column6 k
  · exact AEGIS.CvSAnalyticXColumns0.column7 k
  · exact AEGIS.CvSAnalyticXColumns0.column8 k
  · exact AEGIS.CvSAnalyticXColumns0.column9 k
  · exact AEGIS.CvSAnalyticXColumns1.column10 k
  · exact AEGIS.CvSAnalyticXColumns1.column11 k
  · exact AEGIS.CvSAnalyticXColumns1.column12 k
  · exact AEGIS.CvSAnalyticXColumns1.column13 k
  · exact AEGIS.CvSAnalyticXColumns1.column14 k
  · exact AEGIS.CvSAnalyticXColumns1.column15 k
  · exact AEGIS.CvSAnalyticXColumns1.column16 k
  · exact AEGIS.CvSAnalyticXColumns1.column17 k
  · exact AEGIS.CvSAnalyticXColumns1.column18 k
  · exact AEGIS.CvSAnalyticXColumns1.column19 k
  · exact AEGIS.CvSAnalyticXColumns2.column20 k
  · exact AEGIS.CvSAnalyticXColumns2.column21 k
  · exact AEGIS.CvSAnalyticXColumns2.column22 k
  · exact AEGIS.CvSAnalyticXColumns2.column23 k
  · exact AEGIS.CvSAnalyticXColumns2.column24 k
  · exact AEGIS.CvSAnalyticXColumns2.column25 k
  · exact AEGIS.CvSAnalyticXColumns2.column26 k
  · exact AEGIS.CvSAnalyticXColumns2.column27 k
  · exact AEGIS.CvSAnalyticXColumns2.column28 k
  · exact AEGIS.CvSAnalyticXColumns2.column29 k
  · exact AEGIS.CvSAnalyticXColumns3.column30 k
  · exact AEGIS.CvSAnalyticXColumns3.column31 k
  · exact AEGIS.CvSAnalyticXColumns3.column32 k
  · exact AEGIS.CvSAnalyticXColumns3.column33 k
  · exact AEGIS.CvSAnalyticXColumns3.column34 k
  · exact AEGIS.CvSAnalyticXColumns3.column35 k
  · exact AEGIS.CvSAnalyticXColumns3.column36 k
  · exact AEGIS.CvSAnalyticXColumns3.column37 k
  · exact AEGIS.CvSAnalyticXColumns3.column38 k
  · exact AEGIS.CvSAnalyticXColumns3.column39 k
  · exact AEGIS.CvSAnalyticXColumns4.column40 k
  · exact AEGIS.CvSAnalyticXColumns4.column41 k
  · exact AEGIS.CvSAnalyticXColumns4.column42 k
  · exact AEGIS.CvSAnalyticXColumns4.column43 k
  · exact AEGIS.CvSAnalyticXColumns4.column44 k
  · exact AEGIS.CvSAnalyticXColumns4.column45 k
  · exact AEGIS.CvSAnalyticXColumns4.column46 k
  · exact AEGIS.CvSAnalyticXColumns4.column47 k
  · exact AEGIS.CvSAnalyticXColumns4.column48 k
  · exact AEGIS.CvSAnalyticXColumns4.column49 k
  · exact AEGIS.CvSAnalyticXColumns5.column50 k
  · exact AEGIS.CvSAnalyticXColumns5.column51 k
  · exact AEGIS.CvSAnalyticXColumns5.column52 k
  · exact AEGIS.CvSAnalyticXColumns5.column53 k
  · exact AEGIS.CvSAnalyticXColumns5.column54 k
  · exact AEGIS.CvSAnalyticXColumns5.column55 k
  · exact AEGIS.CvSAnalyticXColumns5.column56 k
  · exact AEGIS.CvSAnalyticXColumns5.column57 k
  · exact AEGIS.CvSAnalyticXColumns5.column58 k
  · exact AEGIS.CvSAnalyticXColumns5.column59 k
  · exact AEGIS.CvSAnalyticXColumns6.column60 k
  · exact AEGIS.CvSAnalyticXColumns6.column61 k
  · exact AEGIS.CvSAnalyticXColumns6.column62 k
  · exact AEGIS.CvSAnalyticXColumns6.column63 k
  · exact AEGIS.CvSAnalyticXColumns6.column64 k
  · exact AEGIS.CvSAnalyticXColumns6.column65 k
  · exact AEGIS.CvSAnalyticXColumns6.column66 k
  · exact AEGIS.CvSAnalyticXColumns6.column67 k
  · exact AEGIS.CvSAnalyticXColumns6.column68 k
  · exact AEGIS.CvSAnalyticXColumns6.column69 k
  · exact AEGIS.CvSAnalyticXColumns7.column70 k
  · exact AEGIS.CvSAnalyticXColumns7.column71 k
  · exact AEGIS.CvSAnalyticXColumns7.column72 k
  · exact AEGIS.CvSAnalyticXColumns7.column73 k
  · exact AEGIS.CvSAnalyticXColumns7.column74 k
  · exact AEGIS.CvSAnalyticXColumns7.column75 k
  · exact AEGIS.CvSAnalyticXColumns7.column76 k
  · exact AEGIS.CvSAnalyticXColumns7.column77 k
  · exact AEGIS.CvSAnalyticXColumns7.column78 k
  · exact AEGIS.CvSAnalyticXColumns7.column79 k
  · exact AEGIS.CvSAnalyticXColumns8.column80 k
  · exact AEGIS.CvSAnalyticXColumns8.column81 k
  · exact AEGIS.CvSAnalyticXColumns8.column82 k
  · exact AEGIS.CvSAnalyticXColumns8.column83 k
  · exact AEGIS.CvSAnalyticXColumns8.column84 k
  · exact AEGIS.CvSAnalyticXColumns8.column85 k
  · exact AEGIS.CvSAnalyticXColumns8.column86 k
  · exact AEGIS.CvSAnalyticXColumns8.column87 k
  · exact AEGIS.CvSAnalyticXColumns8.column88 k
  · exact AEGIS.CvSAnalyticXColumns8.column89 k
  · exact AEGIS.CvSAnalyticXColumns9.column90 k
  · exact AEGIS.CvSAnalyticXColumns9.column91 k
  · exact AEGIS.CvSAnalyticXColumns9.column92 k
  · exact AEGIS.CvSAnalyticXColumns9.column93 k
  · exact AEGIS.CvSAnalyticXColumns9.column94 k
  · exact AEGIS.CvSAnalyticXColumns9.column95 k
  · exact AEGIS.CvSAnalyticXColumns9.column96 k
  · exact AEGIS.CvSAnalyticXColumns9.column97 k
  · exact AEGIS.CvSAnalyticXColumns9.column98 k
  · exact AEGIS.CvSAnalyticXColumns9.column99 k
  · exact AEGIS.CvSAnalyticXColumns10.column100 k
  · exact AEGIS.CvSAnalyticXColumns10.column101 k
  · exact AEGIS.CvSAnalyticXColumns10.column102 k
  · exact AEGIS.CvSAnalyticXColumns10.column103 k
  · exact AEGIS.CvSAnalyticXColumns10.column104 k
  · exact AEGIS.CvSAnalyticXColumns10.column105 k
  · exact AEGIS.CvSAnalyticXColumns10.column106 k
  · exact AEGIS.CvSAnalyticXColumns10.column107 k
  · exact AEGIS.CvSAnalyticXColumns10.column108 k
  · exact AEGIS.CvSAnalyticXColumns10.column109 k
  · exact AEGIS.CvSAnalyticXColumns11.column110 k
  · exact AEGIS.CvSAnalyticXColumns11.column111 k
  · exact AEGIS.CvSAnalyticXColumns11.column112 k
  · exact AEGIS.CvSAnalyticXColumns11.column113 k
  · exact AEGIS.CvSAnalyticXColumns11.column114 k
  · exact AEGIS.CvSAnalyticXColumns11.column115 k
  · exact AEGIS.CvSAnalyticXColumns11.column116 k
  · exact AEGIS.CvSAnalyticXColumns11.column117 k
  · exact AEGIS.CvSAnalyticXColumns11.column118 k
  · exact AEGIS.CvSAnalyticXColumns11.column119 k
  · exact AEGIS.CvSAnalyticXColumns12.column120 k
  · exact AEGIS.CvSAnalyticXColumns12.column121 k
  · exact AEGIS.CvSAnalyticXColumns12.column122 k
  · exact AEGIS.CvSAnalyticXColumns12.column123 k
  · exact AEGIS.CvSAnalyticXColumns12.column124 k
  · exact AEGIS.CvSAnalyticXColumns12.column125 k
  · exact AEGIS.CvSAnalyticXColumns12.column126 k
  · exact AEGIS.CvSAnalyticXColumns12.column127 k
  · exact AEGIS.CvSAnalyticXColumns12.column128 k
  · exact AEGIS.CvSAnalyticXColumns12.column129 k
  · exact AEGIS.CvSAnalyticXColumns13.column130 k
  · exact AEGIS.CvSAnalyticXColumns13.column131 k
  · exact AEGIS.CvSAnalyticXColumns13.column132 k
  · exact AEGIS.CvSAnalyticXColumns13.column133 k
  · exact AEGIS.CvSAnalyticXColumns13.column134 k
  · exact AEGIS.CvSAnalyticXColumns13.column135 k
  · exact AEGIS.CvSAnalyticXColumns13.column136 k
  · exact AEGIS.CvSAnalyticXColumns13.column137 k
  · exact AEGIS.CvSAnalyticXColumns13.column138 k
theorem G_source (k l : Fin 141) :
    (AEGIS.RowBudgetListCell0Pilot.G.getD k.val []).getD l.val ⟨0, 0⟩ =
      AEGIS.CvSRationalIntervalV1.rationalRange 96
        (gramRat 150 (signedFreq k) (signedFreq l)) (gramRat 150 (signedFreq k) (signedFreq l)) := by
  fin_cases k
  · exact AEGIS.CvSAnalyticGRows0.row0 l
  · exact AEGIS.CvSAnalyticGRows0.row1 l
  · exact AEGIS.CvSAnalyticGRows0.row2 l
  · exact AEGIS.CvSAnalyticGRows0.row3 l
  · exact AEGIS.CvSAnalyticGRows0.row4 l
  · exact AEGIS.CvSAnalyticGRows0.row5 l
  · exact AEGIS.CvSAnalyticGRows0.row6 l
  · exact AEGIS.CvSAnalyticGRows0.row7 l
  · exact AEGIS.CvSAnalyticGRows0.row8 l
  · exact AEGIS.CvSAnalyticGRows0.row9 l
  · exact AEGIS.CvSAnalyticGRows1.row10 l
  · exact AEGIS.CvSAnalyticGRows1.row11 l
  · exact AEGIS.CvSAnalyticGRows1.row12 l
  · exact AEGIS.CvSAnalyticGRows1.row13 l
  · exact AEGIS.CvSAnalyticGRows1.row14 l
  · exact AEGIS.CvSAnalyticGRows1.row15 l
  · exact AEGIS.CvSAnalyticGRows1.row16 l
  · exact AEGIS.CvSAnalyticGRows1.row17 l
  · exact AEGIS.CvSAnalyticGRows1.row18 l
  · exact AEGIS.CvSAnalyticGRows1.row19 l
  · exact AEGIS.CvSAnalyticGRows2.row20 l
  · exact AEGIS.CvSAnalyticGRows2.row21 l
  · exact AEGIS.CvSAnalyticGRows2.row22 l
  · exact AEGIS.CvSAnalyticGRows2.row23 l
  · exact AEGIS.CvSAnalyticGRows2.row24 l
  · exact AEGIS.CvSAnalyticGRows2.row25 l
  · exact AEGIS.CvSAnalyticGRows2.row26 l
  · exact AEGIS.CvSAnalyticGRows2.row27 l
  · exact AEGIS.CvSAnalyticGRows2.row28 l
  · exact AEGIS.CvSAnalyticGRows2.row29 l
  · exact AEGIS.CvSAnalyticGRows3.row30 l
  · exact AEGIS.CvSAnalyticGRows3.row31 l
  · exact AEGIS.CvSAnalyticGRows3.row32 l
  · exact AEGIS.CvSAnalyticGRows3.row33 l
  · exact AEGIS.CvSAnalyticGRows3.row34 l
  · exact AEGIS.CvSAnalyticGRows3.row35 l
  · exact AEGIS.CvSAnalyticGRows3.row36 l
  · exact AEGIS.CvSAnalyticGRows3.row37 l
  · exact AEGIS.CvSAnalyticGRows3.row38 l
  · exact AEGIS.CvSAnalyticGRows3.row39 l
  · exact AEGIS.CvSAnalyticGRows4.row40 l
  · exact AEGIS.CvSAnalyticGRows4.row41 l
  · exact AEGIS.CvSAnalyticGRows4.row42 l
  · exact AEGIS.CvSAnalyticGRows4.row43 l
  · exact AEGIS.CvSAnalyticGRows4.row44 l
  · exact AEGIS.CvSAnalyticGRows4.row45 l
  · exact AEGIS.CvSAnalyticGRows4.row46 l
  · exact AEGIS.CvSAnalyticGRows4.row47 l
  · exact AEGIS.CvSAnalyticGRows4.row48 l
  · exact AEGIS.CvSAnalyticGRows4.row49 l
  · exact AEGIS.CvSAnalyticGRows5.row50 l
  · exact AEGIS.CvSAnalyticGRows5.row51 l
  · exact AEGIS.CvSAnalyticGRows5.row52 l
  · exact AEGIS.CvSAnalyticGRows5.row53 l
  · exact AEGIS.CvSAnalyticGRows5.row54 l
  · exact AEGIS.CvSAnalyticGRows5.row55 l
  · exact AEGIS.CvSAnalyticGRows5.row56 l
  · exact AEGIS.CvSAnalyticGRows5.row57 l
  · exact AEGIS.CvSAnalyticGRows5.row58 l
  · exact AEGIS.CvSAnalyticGRows5.row59 l
  · exact AEGIS.CvSAnalyticGRows6.row60 l
  · exact AEGIS.CvSAnalyticGRows6.row61 l
  · exact AEGIS.CvSAnalyticGRows6.row62 l
  · exact AEGIS.CvSAnalyticGRows6.row63 l
  · exact AEGIS.CvSAnalyticGRows6.row64 l
  · exact AEGIS.CvSAnalyticGRows6.row65 l
  · exact AEGIS.CvSAnalyticGRows6.row66 l
  · exact AEGIS.CvSAnalyticGRows6.row67 l
  · exact AEGIS.CvSAnalyticGRows6.row68 l
  · exact AEGIS.CvSAnalyticGRows6.row69 l
  · exact AEGIS.CvSAnalyticGRows7.row70 l
  · exact AEGIS.CvSAnalyticGRows7.row71 l
  · exact AEGIS.CvSAnalyticGRows7.row72 l
  · exact AEGIS.CvSAnalyticGRows7.row73 l
  · exact AEGIS.CvSAnalyticGRows7.row74 l
  · exact AEGIS.CvSAnalyticGRows7.row75 l
  · exact AEGIS.CvSAnalyticGRows7.row76 l
  · exact AEGIS.CvSAnalyticGRows7.row77 l
  · exact AEGIS.CvSAnalyticGRows7.row78 l
  · exact AEGIS.CvSAnalyticGRows7.row79 l
  · exact AEGIS.CvSAnalyticGRows8.row80 l
  · exact AEGIS.CvSAnalyticGRows8.row81 l
  · exact AEGIS.CvSAnalyticGRows8.row82 l
  · exact AEGIS.CvSAnalyticGRows8.row83 l
  · exact AEGIS.CvSAnalyticGRows8.row84 l
  · exact AEGIS.CvSAnalyticGRows8.row85 l
  · exact AEGIS.CvSAnalyticGRows8.row86 l
  · exact AEGIS.CvSAnalyticGRows8.row87 l
  · exact AEGIS.CvSAnalyticGRows8.row88 l
  · exact AEGIS.CvSAnalyticGRows8.row89 l
  · exact AEGIS.CvSAnalyticGRows9.row90 l
  · exact AEGIS.CvSAnalyticGRows9.row91 l
  · exact AEGIS.CvSAnalyticGRows9.row92 l
  · exact AEGIS.CvSAnalyticGRows9.row93 l
  · exact AEGIS.CvSAnalyticGRows9.row94 l
  · exact AEGIS.CvSAnalyticGRows9.row95 l
  · exact AEGIS.CvSAnalyticGRows9.row96 l
  · exact AEGIS.CvSAnalyticGRows9.row97 l
  · exact AEGIS.CvSAnalyticGRows9.row98 l
  · exact AEGIS.CvSAnalyticGRows9.row99 l
  · exact AEGIS.CvSAnalyticGRows10.row100 l
  · exact AEGIS.CvSAnalyticGRows10.row101 l
  · exact AEGIS.CvSAnalyticGRows10.row102 l
  · exact AEGIS.CvSAnalyticGRows10.row103 l
  · exact AEGIS.CvSAnalyticGRows10.row104 l
  · exact AEGIS.CvSAnalyticGRows10.row105 l
  · exact AEGIS.CvSAnalyticGRows10.row106 l
  · exact AEGIS.CvSAnalyticGRows10.row107 l
  · exact AEGIS.CvSAnalyticGRows10.row108 l
  · exact AEGIS.CvSAnalyticGRows10.row109 l
  · exact AEGIS.CvSAnalyticGRows11.row110 l
  · exact AEGIS.CvSAnalyticGRows11.row111 l
  · exact AEGIS.CvSAnalyticGRows11.row112 l
  · exact AEGIS.CvSAnalyticGRows11.row113 l
  · exact AEGIS.CvSAnalyticGRows11.row114 l
  · exact AEGIS.CvSAnalyticGRows11.row115 l
  · exact AEGIS.CvSAnalyticGRows11.row116 l
  · exact AEGIS.CvSAnalyticGRows11.row117 l
  · exact AEGIS.CvSAnalyticGRows11.row118 l
  · exact AEGIS.CvSAnalyticGRows11.row119 l
  · exact AEGIS.CvSAnalyticGRows12.row120 l
  · exact AEGIS.CvSAnalyticGRows12.row121 l
  · exact AEGIS.CvSAnalyticGRows12.row122 l
  · exact AEGIS.CvSAnalyticGRows12.row123 l
  · exact AEGIS.CvSAnalyticGRows12.row124 l
  · exact AEGIS.CvSAnalyticGRows12.row125 l
  · exact AEGIS.CvSAnalyticGRows12.row126 l
  · exact AEGIS.CvSAnalyticGRows12.row127 l
  · exact AEGIS.CvSAnalyticGRows12.row128 l
  · exact AEGIS.CvSAnalyticGRows12.row129 l
  · exact AEGIS.CvSAnalyticGRows13.row130 l
  · exact AEGIS.CvSAnalyticGRows13.row131 l
  · exact AEGIS.CvSAnalyticGRows13.row132 l
  · exact AEGIS.CvSAnalyticGRows13.row133 l
  · exact AEGIS.CvSAnalyticGRows13.row134 l
  · exact AEGIS.CvSAnalyticGRows13.row135 l
  · exact AEGIS.CvSAnalyticGRows13.row136 l
  · exact AEGIS.CvSAnalyticGRows13.row137 l
  · exact AEGIS.CvSAnalyticGRows13.row138 l
  · exact AEGIS.CvSAnalyticGRows13.row139 l
  · exact AEGIS.CvSAnalyticGRows14.row140 l
/-- Staged interval products coincide with the already-proved actual source box formulas. -/
theorem Y_source (r : Fin 301) (i : Fin 139) : Y r i = sourceYBox 96 (rowIndex r) i := by
  rw [Y_entry, listDot_eq_dot 96 _ _ (eRow r).length_eq (inputColumn i).x.length_eq]
  change dot 96 (fun k : Fin 141 => (eRow r).values.getD k.val ⟨0, 0⟩)
    (fun k : Fin 141 => (inputColumn i).x.values.getD k.val ⟨0, 0⟩) =
    dot 96 (kernelBox 96 (rowIndex r)) (fun k => xBox k i)
  congr 1
  · funext k; exact E_source r k
  · funext k; exact X_source k i

theorem inner_source (k : Fin 141) (i : Fin 139) : inner k.val i =
    dot 96 (xBox k) (fun j => lambdaBox j i) := by
  rw [inner_entry, listDot_eq_dot 96 _ _ (xRow k).length_eq (lambdaColumn i).length_eq]
  change dot 96 (fun j => (xRow k).values.getD j.val ⟨0, 0⟩)
    (fun j => lambdaBox j i) = dot 96 (xBox k) (fun j => lambdaBox j i)
  congr 1
  funext j
  exact (x_transpose k j).trans (X_source k j)

theorem Z_source (r : Fin 301) (i : Fin 139) :
    (inputColumn i).z.values.getD r.val ⟨0, 0⟩ = zBox lambdaBox r i := by
  rw [Z_entry]
  unfold zBox
  split_ifs with hr
  · rw [Y_source, inner_source (⟨r.val - 80, by omega⟩ : Fin 141) i]
  · exact Y_source r i

theorem X_mem (k : Fin 141) (i : Fin 139) :
    ((inputColumn i).x.values.getD k.val ⟨0, 0⟩).Mem 96 (transformedCoeff k i) := by
  rw [X_source]
  exact transformedCoeff_mem 96 k i

theorem Y_mem (M : ℕ) (hM : 3 ≤ M) (r : Fin 301) (i : Fin 139) :
    (Y r i).Mem 96 (AEGIS.CvSActualCrossRowL12V1.sourceY M (rowIndex r) i) := by
  rw [Y_source]
  have hm : (rowIndex r).natAbs ≤ 150 := by
    unfold rowIndex
    have hr := r.isLt
    omega
  exact sourceY_mem 96 hM (rowIndex r) hm i

theorem Z_mem (M : ℕ) (hM : 3 ≤ M) (r : Fin 301) (i : Fin 139) :
    ((inputColumn i).z.values.getD r.val ⟨0, 0⟩).Mem 96 (sourceZ M lambdaReal r i) := by
  rw [Z_source]
  exact sourceZ_mem M hM lambdaReal lambdaBox lambda_mem r i

theorem G_mem (k l : Fin 141) :
    ((AEGIS.RowBudgetListCell0Pilot.G.getD k.val []).getD l.val ⟨0, 0⟩).Mem 96
      (AEGIS.CvSGramTailV1.gramUp 150 (signedFreq k) (signedFreq l)) := by
  rw [G_source]
  exact gramUp_mem 96 150 (signedFreq k) (signedFreq l)

theorem T_mem (M : ℕ) (hM : 3 ≤ M) (k : Fin 141) :
    (AEGIS.RowBudgetStagedDotPilot.T.getD k.val ⟨0, 0⟩).Mem 96
      (AEGIS.CvSRowTailV1.tau M (6/5) (signedFreq k)) := by
  rw [AEGIS.CvSAnalyticScalarInputsV1.tau_source]
  have hk : (signedFreq k).natAbs ≤ 150 := by
    have h := k.isLt
    unfold signedFreq
    omega
  exact AEGIS.CvSTauSigned150L12V1.signed_tau_interval 96 hM (signedFreq k) hk

theorem LP_mem : AEGIS.RowBudgetListCell0Pilot.LP2.Mem 96 (((6/5 : ℝ)/Real.pi)^2) := by
  rw [AEGIS.CvSAnalyticScalarInputsV1.lp_source]
  exact AEGIS.CvSFrequencyIntervalV1.lp_squared_mem 96

/-- The actual cross kernel includes 2*pi; it must not be identified with signedEntry. -/
theorem sourceKernel_signed (M : ℕ) (k l : Fin 141) :
    AEGIS.CvSActualCrossRowL12V1.sourceKernel M (signedFreq k) (signedFreq l) =
      2 * Real.pi * signedEntry M k l := by
  unfold AEGIS.CvSActualCrossRowL12V1.sourceKernel signedEntry
  rw [AEGIS.CvSRowTailV1.cvsEntry_symm M (by norm_num : (0 : ℝ) < 6/5)
    (signedFreq l) (signedFreq k)]
  ring

theorem projectedEntry_as_Y (M : ℕ) (i j : Fin 139) :
    (∑ k : Fin 141, transformedCoeff k i *
      AEGIS.CvSActualCrossRowL12V1.sourceY M (signedFreq k) j) =
      2 * Real.pi * projectedEntry M i j := by
  simp only [AEGIS.CvSActualCrossRowL12V1.sourceY, projectedEntry, sourceKernel_signed,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem Q_mem (M : ℕ) (hM : 3 ≤ M) (i j : Fin 139) :
    (AEGIS.CvSFullTableClosureV1.Q i j).Mem 96 (projectedEntry M i j) := by
  apply mem_of_contains 96 (AEGIS.CvSSourceQAllV1.checked i j)
  apply normalize_mem
  rw [evalDot_eq (by decide : 0 < 141) (by decide : 141 ≤ 301),
    listDot_eq_dot 96 _ _ (inputColumn i).x.length_eq (AEGIS.CvSSourceQAllV1.vector j).length_eq]
  rw [← projectedEntry_as_Y M i j]
  apply dot_mem 96 _ _ (fun k => transformedCoeff k i)
    (fun k => AEGIS.CvSActualCrossRowL12V1.sourceY M (signedFreq k) j) (fun k => X_mem k i)
  intro k
  rw [AEGIS.CvSSourceQAllV1.vector_source]
  have h := Y_mem M hM (⟨k.val + 80, by omega⟩ : Fin 301) j
  have he : rowIndex (⟨k.val + 80, by omega⟩ : Fin 301) = signedFreq k := by
    change ((k.val + 80 : ℕ) : ℤ) - 150 = (k.val : ℤ) - 70
    omega
  rw [he] at h
  exact h

/-- All literal source memberships discharged; a quantitative bound on the actual finite CvS residual. -/
theorem actual_budgetEnergy_margin (M : ℕ) (hM : 3 ≤ M) (v : Fin 139 → ℂ) :
    AEGIS.CvSStrictRowBudgetV1.margin * (∑ i, ‖v i‖^2) +
      AEGIS.CvSRowBudgetGramBridgeV1.budgetEnergy (sourceZ M lambdaReal)
        (AEGIS.CvSRealTailMatrixV1.tailMatrix transformedCoeff
          (fun k l => AEGIS.CvSGramTailV1.gramUp 150 (signedFreq k) (signedFreq l))
          (fun k => AEGIS.CvSRowTailV1.tau M (6/5) (signedFreq k)) (((6/5 : ℝ)/Real.pi)^2)) v ≤
      40 * (∑ i, ∑ j, v i * conj (v j) * (projectedEntry M i j : ℂ)).re := by
  exact AEGIS.CvSFullBudgetJoinV1.budgetEnergy_margin_le_of_inputs
    (projectedEntry M) transformedCoeff
    (fun k l => AEGIS.CvSGramTailV1.gramUp 150 (signedFreq k) (signedFreq l))
    (fun k => AEGIS.CvSRowTailV1.tau M (6/5) (signedFreq k))
    (sourceZ M lambdaReal) (((6/5 : ℝ)/Real.pi)^2)
    (AEGIS.CvSProjectedSymmetryV1.projectedEntry_symm M)
    (fun k l => gramUp_symm 150 (signedFreq k) (signedFreq l))
    (Q_mem M hM) X_mem G_mem (T_mem M hM) (Z_mem M hM) LP_mem v
end AEGIS.CvSActualLiteralInputsV1
#check @AEGIS.CvSActualLiteralInputsV1.E_source
#print axioms AEGIS.CvSActualLiteralInputsV1.E_source
#check @AEGIS.CvSActualLiteralInputsV1.X_source
#print axioms AEGIS.CvSActualLiteralInputsV1.X_source
#check @AEGIS.CvSActualLiteralInputsV1.G_source
#print axioms AEGIS.CvSActualLiteralInputsV1.G_source
#check @AEGIS.CvSActualLiteralInputsV1.Y_source
#print axioms AEGIS.CvSActualLiteralInputsV1.Y_source
#check @AEGIS.CvSActualLiteralInputsV1.inner_source
#print axioms AEGIS.CvSActualLiteralInputsV1.inner_source
#check @AEGIS.CvSActualLiteralInputsV1.Z_source
#print axioms AEGIS.CvSActualLiteralInputsV1.Z_source
#check @AEGIS.CvSActualLiteralInputsV1.X_mem
#print axioms AEGIS.CvSActualLiteralInputsV1.X_mem
#check @AEGIS.CvSActualLiteralInputsV1.Y_mem
#print axioms AEGIS.CvSActualLiteralInputsV1.Y_mem
#check @AEGIS.CvSActualLiteralInputsV1.Z_mem
#print axioms AEGIS.CvSActualLiteralInputsV1.Z_mem
#check @AEGIS.CvSActualLiteralInputsV1.G_mem
#print axioms AEGIS.CvSActualLiteralInputsV1.G_mem
#check @AEGIS.CvSActualLiteralInputsV1.T_mem
#print axioms AEGIS.CvSActualLiteralInputsV1.T_mem
#check @AEGIS.CvSActualLiteralInputsV1.LP_mem
#print axioms AEGIS.CvSActualLiteralInputsV1.LP_mem
#check @AEGIS.CvSActualLiteralInputsV1.sourceKernel_signed
#print axioms AEGIS.CvSActualLiteralInputsV1.sourceKernel_signed
#check @AEGIS.CvSActualLiteralInputsV1.projectedEntry_as_Y
#print axioms AEGIS.CvSActualLiteralInputsV1.projectedEntry_as_Y
#check @AEGIS.CvSActualLiteralInputsV1.Q_mem
#print axioms AEGIS.CvSActualLiteralInputsV1.Q_mem
#check @AEGIS.CvSActualLiteralInputsV1.actual_budgetEnergy_margin
#print axioms AEGIS.CvSActualLiteralInputsV1.actual_budgetEnergy_margin
