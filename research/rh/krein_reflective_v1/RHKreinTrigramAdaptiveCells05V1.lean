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
import RHKreinTrigramAdaptiveCells04V1

set_option autoImplicit false
noncomputable section
namespace AEGIS.RHKreinTrigramAdaptiveV1
open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinCellBatchV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinFirstCellV1
open AEGIS.RHKreinSecondCellReductionV1

theorem c0190 : checkPiece pa19 (675/128) 0 (675/128) (2775/512) = true := by decide +kernel
theorem n0190 : NonnegOnQ (675/128) (2775/512) :=
  nonnegOn_of_checkPiece_zero (675/128) (2775/512) (by norm_num) c0190

theorem c0191 : checkPiece pa19 (2775/512) 0 (2775/512) (1425/256) = true := by decide +kernel
theorem n0191 : NonnegOnQ (2775/512) (1425/256) :=
  nonnegOn_of_checkPiece_zero (2775/512) (1425/256) (by norm_num) c0191

theorem c0192 : checkPiece pa19 (1425/256) 0 (1425/256) (2925/512) = true := by decide +kernel
theorem n0192 : NonnegOnQ (1425/256) (2925/512) :=
  nonnegOn_of_checkPiece_zero (1425/256) (2925/512) (by norm_num) c0192

theorem c0193 : checkPiece pa19 (2925/512) 0 (2925/512) (375/64) = true := by decide +kernel
theorem n0193 : NonnegOnQ (2925/512) (375/64) :=
  nonnegOn_of_checkPiece_zero (2925/512) (375/64) (by norm_num) c0193

theorem c0194 : checkPiece pa19 (375/64) 0 (375/64) (3075/512) = true := by decide +kernel
theorem n0194 : NonnegOnQ (375/64) (3075/512) :=
  nonnegOn_of_checkPiece_zero (375/64) (3075/512) (by norm_num) c0194

theorem c0195 : checkPiece pa19 (3075/512) 0 (3075/512) (1575/256) = true := by decide +kernel
theorem n0195 : NonnegOnQ (3075/512) (1575/256) :=
  nonnegOn_of_checkPiece_zero (3075/512) (1575/256) (by norm_num) c0195

theorem c0196 : checkPiece pa19 (1575/256) 0 (1575/256) (3225/512) = true := by decide +kernel
theorem n0196 : NonnegOnQ (1575/256) (3225/512) :=
  nonnegOn_of_checkPiece_zero (1575/256) (3225/512) (by norm_num) c0196

theorem c0197 : checkPiece pa19 (3225/512) 0 (3225/512) (825/128) = true := by decide +kernel
theorem n0197 : NonnegOnQ (3225/512) (825/128) :=
  nonnegOn_of_checkPiece_zero (3225/512) (825/128) (by norm_num) c0197

theorem c0198 : checkPiece pa19 (825/128) 0 (825/128) (3375/512) = true := by decide +kernel
theorem n0198 : NonnegOnQ (825/128) (3375/512) :=
  nonnegOn_of_checkPiece_zero (825/128) (3375/512) (by norm_num) c0198

theorem c0199 : checkPiece pa19 (3375/512) 0 (3375/512) (1725/256) = true := by decide +kernel
theorem n0199 : NonnegOnQ (3375/512) (1725/256) :=
  nonnegOn_of_checkPiece_zero (3375/512) (1725/256) (by norm_num) c0199

theorem c0200 : checkPiece pa19 (1725/256) 0 (1725/256) (3525/512) = true := by decide +kernel
theorem n0200 : NonnegOnQ (1725/256) (3525/512) :=
  nonnegOn_of_checkPiece_zero (1725/256) (3525/512) (by norm_num) c0200

theorem c0201 : checkPiece pa19 (3525/512) 0 (3525/512) (225/32) = true := by decide +kernel
theorem n0201 : NonnegOnQ (3525/512) (225/32) :=
  nonnegOn_of_checkPiece_zero (3525/512) (225/32) (by norm_num) c0201

theorem c0202 : checkPiece pa19 (225/32) 0 (225/32) (3675/512) = true := by decide +kernel
theorem n0202 : NonnegOnQ (225/32) (3675/512) :=
  nonnegOn_of_checkPiece_zero (225/32) (3675/512) (by norm_num) c0202

theorem c0203 : checkPiece pa19 (3675/512) 0 (3675/512) (1875/256) = true := by decide +kernel
theorem n0203 : NonnegOnQ (3675/512) (1875/256) :=
  nonnegOn_of_checkPiece_zero (3675/512) (1875/256) (by norm_num) c0203

theorem c0204 : checkPiece pa19 (1875/256) 0 (1875/256) (3825/512) = true := by decide +kernel
theorem n0204 : NonnegOnQ (1875/256) (3825/512) :=
  nonnegOn_of_checkPiece_zero (1875/256) (3825/512) (by norm_num) c0204

theorem c0205 : checkPiece pa19 (3825/512) 0 (3825/512) (975/128) = true := by decide +kernel
theorem n0205 : NonnegOnQ (3825/512) (975/128) :=
  nonnegOn_of_checkPiece_zero (3825/512) (975/128) (by norm_num) c0205

theorem c0206 : checkPiece pa19 (975/128) 0 (975/128) (3975/512) = true := by decide +kernel
theorem n0206 : NonnegOnQ (975/128) (3975/512) :=
  nonnegOn_of_checkPiece_zero (975/128) (3975/512) (by norm_num) c0206

theorem c0207 : checkPiece pa19 (3975/512) 0 (3975/512) (2025/256) = true := by decide +kernel
theorem n0207 : NonnegOnQ (3975/512) (2025/256) :=
  nonnegOn_of_checkPiece_zero (3975/512) (2025/256) (by norm_num) c0207

theorem c0208 : checkPiece pa19 (2025/256) 0 (2025/256) (4125/512) = true := by decide +kernel
theorem n0208 : NonnegOnQ (2025/256) (4125/512) :=
  nonnegOn_of_checkPiece_zero (2025/256) (4125/512) (by norm_num) c0208

theorem c0209 : checkPiece pa19 (4125/512) 0 (4125/512) (525/64) = true := by decide +kernel
theorem n0209 : NonnegOnQ (4125/512) (525/64) :=
  nonnegOn_of_checkPiece_zero (4125/512) (525/64) (by norm_num) c0209

theorem c0210 : checkPiece pa19 (525/64) 0 (525/64) (4275/512) = true := by decide +kernel
theorem n0210 : NonnegOnQ (525/64) (4275/512) :=
  nonnegOn_of_checkPiece_zero (525/64) (4275/512) (by norm_num) c0210

theorem c0211 : checkPiece pa19 (4275/512) 0 (4275/512) (2175/256) = true := by decide +kernel
theorem n0211 : NonnegOnQ (4275/512) (2175/256) :=
  nonnegOn_of_checkPiece_zero (4275/512) (2175/256) (by norm_num) c0211

theorem c0212 : checkPiece pa19 (2175/256) 0 (2175/256) (4425/512) = true := by decide +kernel
theorem n0212 : NonnegOnQ (2175/256) (4425/512) :=
  nonnegOn_of_checkPiece_zero (2175/256) (4425/512) (by norm_num) c0212

theorem c0213 : checkPiece pa19 (4425/512) 0 (4425/512) (1125/128) = true := by decide +kernel
theorem n0213 : NonnegOnQ (4425/512) (1125/128) :=
  nonnegOn_of_checkPiece_zero (4425/512) (1125/128) (by norm_num) c0213

theorem c0214 : checkPiece pa19 (1125/128) 0 (1125/128) (4575/512) = true := by decide +kernel
theorem n0214 : NonnegOnQ (1125/128) (4575/512) :=
  nonnegOn_of_checkPiece_zero (1125/128) (4575/512) (by norm_num) c0214

theorem c0215 : checkPiece pa19 (4575/512) 0 (4575/512) (2325/256) = true := by decide +kernel
theorem n0215 : NonnegOnQ (4575/512) (2325/256) :=
  nonnegOn_of_checkPiece_zero (4575/512) (2325/256) (by norm_num) c0215

theorem c0216 : checkPiece pa19 (2325/256) 0 (2325/256) (4725/512) = true := by decide +kernel
theorem n0216 : NonnegOnQ (2325/256) (4725/512) :=
  nonnegOn_of_checkPiece_zero (2325/256) (4725/512) (by norm_num) c0216

theorem c0217 : checkPiece pa19 (4725/512) 0 (4725/512) (75/8) = true := by decide +kernel
theorem n0217 : NonnegOnQ (4725/512) (75/8) :=
  nonnegOn_of_checkPiece_zero (4725/512) (75/8) (by norm_num) c0217

theorem c0218 : checkPiece pa19 (75/8) 0 (75/8) (4875/512) = true := by decide +kernel
theorem n0218 : NonnegOnQ (75/8) (4875/512) :=
  nonnegOn_of_checkPiece_zero (75/8) (4875/512) (by norm_num) c0218

theorem c0219 : checkPiece pa19 (4875/512) 0 (4875/512) (2475/256) = true := by decide +kernel
theorem n0219 : NonnegOnQ (4875/512) (2475/256) :=
  nonnegOn_of_checkPiece_zero (4875/512) (2475/256) (by norm_num) c0219

theorem c0220 : checkPiece pa19 (2475/256) 0 (2475/256) (1275/128) = true := by decide +kernel
theorem n0220 : NonnegOnQ (2475/256) (1275/128) :=
  nonnegOn_of_checkPiece_zero (2475/256) (1275/128) (by norm_num) c0220

theorem c0221 : checkPiece pa19 (1275/128) 0 (1275/128) (2625/256) = true := by decide +kernel
theorem n0221 : NonnegOnQ (1275/128) (2625/256) :=
  nonnegOn_of_checkPiece_zero (1275/128) (2625/256) (by norm_num) c0221

theorem c0222 : checkPiece pa19 (2625/256) 0 (2625/256) (675/64) = true := by decide +kernel
theorem n0222 : NonnegOnQ (2625/256) (675/64) :=
  nonnegOn_of_checkPiece_zero (2625/256) (675/64) (by norm_num) c0222

theorem c0223 : checkPiece pa19 (675/64) 0 (675/64) (2775/256) = true := by decide +kernel
theorem n0223 : NonnegOnQ (675/64) (2775/256) :=
  nonnegOn_of_checkPiece_zero (675/64) (2775/256) (by norm_num) c0223

theorem c0224 : checkPiece pa19 (2775/256) 0 (2775/256) (1425/128) = true := by decide +kernel
theorem n0224 : NonnegOnQ (2775/256) (1425/128) :=
  nonnegOn_of_checkPiece_zero (2775/256) (1425/128) (by norm_num) c0224

theorem c0225 : checkPiece pa19 (1425/128) 0 (1425/128) (2925/256) = true := by decide +kernel
theorem n0225 : NonnegOnQ (1425/128) (2925/256) :=
  nonnegOn_of_checkPiece_zero (1425/128) (2925/256) (by norm_num) c0225

theorem c0226 : checkPiece pa19 (2925/256) 0 (2925/256) (375/32) = true := by decide +kernel
theorem n0226 : NonnegOnQ (2925/256) (375/32) :=
  nonnegOn_of_checkPiece_zero (2925/256) (375/32) (by norm_num) c0226

theorem c0227 : checkPiece pa19 (375/32) 0 (375/32) (3075/256) = true := by decide +kernel
theorem n0227 : NonnegOnQ (375/32) (3075/256) :=
  nonnegOn_of_checkPiece_zero (375/32) (3075/256) (by norm_num) c0227

theorem c0228 : checkPiece pa19 (3075/256) 0 (3075/256) (1575/128) = true := by decide +kernel
theorem n0228 : NonnegOnQ (3075/256) (1575/128) :=
  nonnegOn_of_checkPiece_zero (3075/256) (1575/128) (by norm_num) c0228

theorem c0229 : checkPiece pa19 (1575/128) 0 (1575/128) (3225/256) = true := by decide +kernel
theorem n0229 : NonnegOnQ (1575/128) (3225/256) :=
  nonnegOn_of_checkPiece_zero (1575/128) (3225/256) (by norm_num) c0229

theorem c0230 : checkPiece pa19 (3225/256) 0 (3225/256) (825/64) = true := by decide +kernel
theorem n0230 : NonnegOnQ (3225/256) (825/64) :=
  nonnegOn_of_checkPiece_zero (3225/256) (825/64) (by norm_num) c0230

theorem c0231 : checkPiece pa19 (825/64) 0 (825/64) (6675/512) = true := by decide +kernel
theorem n0231 : NonnegOnQ (825/64) (6675/512) :=
  nonnegOn_of_checkPiece_zero (825/64) (6675/512) (by norm_num) c0231

theorem c0232 : checkPiece pa19 (6675/512) 0 (6675/512) (3375/256) = true := by decide +kernel
theorem n0232 : NonnegOnQ (6675/512) (3375/256) :=
  nonnegOn_of_checkPiece_zero (6675/512) (3375/256) (by norm_num) c0232

theorem c0233 : checkPiece pa19 (3375/256) 0 (3375/256) (6825/512) = true := by decide +kernel
theorem n0233 : NonnegOnQ (3375/256) (6825/512) :=
  nonnegOn_of_checkPiece_zero (3375/256) (6825/512) (by norm_num) c0233

theorem c0234 : checkPiece pa19 (6825/512) 0 (6825/512) (1725/128) = true := by decide +kernel
theorem n0234 : NonnegOnQ (6825/512) (1725/128) :=
  nonnegOn_of_checkPiece_zero (6825/512) (1725/128) (by norm_num) c0234

theorem c0235 : checkPiece pa19 (1725/128) 0 (1725/128) (3525/256) = true := by decide +kernel
theorem n0235 : NonnegOnQ (1725/128) (3525/256) :=
  nonnegOn_of_checkPiece_zero (1725/128) (3525/256) (by norm_num) c0235

theorem c0236 : checkPiece pa19 (3525/256) 0 (3525/256) (225/16) = true := by decide +kernel
theorem n0236 : NonnegOnQ (3525/256) (225/16) :=
  nonnegOn_of_checkPiece_zero (3525/256) (225/16) (by norm_num) c0236

/- Original contiguous interval fold, staged to bound Lean memory use. -/
set_option maxRecDepth 4096 in
theorem foldTo0236 : NonnegOnQ 0 (225/16) := by
  have h189 := foldTo0189
  have h190 : NonnegOnQ 0 (2775/512) := nonnegOn_union 0 (675/128) (2775/512) h189 n0190
  have h191 : NonnegOnQ 0 (1425/256) := nonnegOn_union 0 (2775/512) (1425/256) h190 n0191
  have h192 : NonnegOnQ 0 (2925/512) := nonnegOn_union 0 (1425/256) (2925/512) h191 n0192
  have h193 : NonnegOnQ 0 (375/64) := nonnegOn_union 0 (2925/512) (375/64) h192 n0193
  have h194 : NonnegOnQ 0 (3075/512) := nonnegOn_union 0 (375/64) (3075/512) h193 n0194
  have h195 : NonnegOnQ 0 (1575/256) := nonnegOn_union 0 (3075/512) (1575/256) h194 n0195
  have h196 : NonnegOnQ 0 (3225/512) := nonnegOn_union 0 (1575/256) (3225/512) h195 n0196
  have h197 : NonnegOnQ 0 (825/128) := nonnegOn_union 0 (3225/512) (825/128) h196 n0197
  have h198 : NonnegOnQ 0 (3375/512) := nonnegOn_union 0 (825/128) (3375/512) h197 n0198
  have h199 : NonnegOnQ 0 (1725/256) := nonnegOn_union 0 (3375/512) (1725/256) h198 n0199
  have h200 : NonnegOnQ 0 (3525/512) := nonnegOn_union 0 (1725/256) (3525/512) h199 n0200
  have h201 : NonnegOnQ 0 (225/32) := nonnegOn_union 0 (3525/512) (225/32) h200 n0201
  have h202 : NonnegOnQ 0 (3675/512) := nonnegOn_union 0 (225/32) (3675/512) h201 n0202
  have h203 : NonnegOnQ 0 (1875/256) := nonnegOn_union 0 (3675/512) (1875/256) h202 n0203
  have h204 : NonnegOnQ 0 (3825/512) := nonnegOn_union 0 (1875/256) (3825/512) h203 n0204
  have h205 : NonnegOnQ 0 (975/128) := nonnegOn_union 0 (3825/512) (975/128) h204 n0205
  have h206 : NonnegOnQ 0 (3975/512) := nonnegOn_union 0 (975/128) (3975/512) h205 n0206
  have h207 : NonnegOnQ 0 (2025/256) := nonnegOn_union 0 (3975/512) (2025/256) h206 n0207
  have h208 : NonnegOnQ 0 (4125/512) := nonnegOn_union 0 (2025/256) (4125/512) h207 n0208
  have h209 : NonnegOnQ 0 (525/64) := nonnegOn_union 0 (4125/512) (525/64) h208 n0209
  have h210 : NonnegOnQ 0 (4275/512) := nonnegOn_union 0 (525/64) (4275/512) h209 n0210
  have h211 : NonnegOnQ 0 (2175/256) := nonnegOn_union 0 (4275/512) (2175/256) h210 n0211
  have h212 : NonnegOnQ 0 (4425/512) := nonnegOn_union 0 (2175/256) (4425/512) h211 n0212
  have h213 : NonnegOnQ 0 (1125/128) := nonnegOn_union 0 (4425/512) (1125/128) h212 n0213
  have h214 : NonnegOnQ 0 (4575/512) := nonnegOn_union 0 (1125/128) (4575/512) h213 n0214
  have h215 : NonnegOnQ 0 (2325/256) := nonnegOn_union 0 (4575/512) (2325/256) h214 n0215
  have h216 : NonnegOnQ 0 (4725/512) := nonnegOn_union 0 (2325/256) (4725/512) h215 n0216
  have h217 : NonnegOnQ 0 (75/8) := nonnegOn_union 0 (4725/512) (75/8) h216 n0217
  have h218 : NonnegOnQ 0 (4875/512) := nonnegOn_union 0 (75/8) (4875/512) h217 n0218
  have h219 : NonnegOnQ 0 (2475/256) := nonnegOn_union 0 (4875/512) (2475/256) h218 n0219
  have h220 : NonnegOnQ 0 (1275/128) := nonnegOn_union 0 (2475/256) (1275/128) h219 n0220
  have h221 : NonnegOnQ 0 (2625/256) := nonnegOn_union 0 (1275/128) (2625/256) h220 n0221
  have h222 : NonnegOnQ 0 (675/64) := nonnegOn_union 0 (2625/256) (675/64) h221 n0222
  have h223 : NonnegOnQ 0 (2775/256) := nonnegOn_union 0 (675/64) (2775/256) h222 n0223
  have h224 : NonnegOnQ 0 (1425/128) := nonnegOn_union 0 (2775/256) (1425/128) h223 n0224
  have h225 : NonnegOnQ 0 (2925/256) := nonnegOn_union 0 (1425/128) (2925/256) h224 n0225
  have h226 : NonnegOnQ 0 (375/32) := nonnegOn_union 0 (2925/256) (375/32) h225 n0226
  have h227 : NonnegOnQ 0 (3075/256) := nonnegOn_union 0 (375/32) (3075/256) h226 n0227
  have h228 : NonnegOnQ 0 (1575/128) := nonnegOn_union 0 (3075/256) (1575/128) h227 n0228
  have h229 : NonnegOnQ 0 (3225/256) := nonnegOn_union 0 (1575/128) (3225/256) h228 n0229
  have h230 : NonnegOnQ 0 (825/64) := nonnegOn_union 0 (3225/256) (825/64) h229 n0230
  have h231 : NonnegOnQ 0 (6675/512) := nonnegOn_union 0 (825/64) (6675/512) h230 n0231
  have h232 : NonnegOnQ 0 (3375/256) := nonnegOn_union 0 (6675/512) (3375/256) h231 n0232
  have h233 : NonnegOnQ 0 (6825/512) := nonnegOn_union 0 (3375/256) (6825/512) h232 n0233
  have h234 : NonnegOnQ 0 (1725/128) := nonnegOn_union 0 (6825/512) (1725/128) h233 n0234
  have h235 : NonnegOnQ 0 (3525/256) := nonnegOn_union 0 (1725/128) (3525/256) h234 n0235
  have h236 : NonnegOnQ 0 (225/16) := nonnegOn_union 0 (3525/256) (225/16) h235 n0236
  exact h236

end AEGIS.RHKreinTrigramAdaptiveV1
