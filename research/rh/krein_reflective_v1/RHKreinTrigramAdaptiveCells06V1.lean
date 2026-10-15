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
import RHKreinTrigramAdaptiveCells05V1

set_option autoImplicit false
noncomputable section
namespace AEGIS.RHKreinTrigramAdaptiveV1
open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinCellBatchV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinFirstCellV1
open AEGIS.RHKreinSecondCellReductionV1

theorem c0237 : checkPiece pa19 (225/16) 0 (225/16) (3675/256) = true := by decide +kernel
theorem n0237 : NonnegOnQ (225/16) (3675/256) :=
  nonnegOn_of_checkPiece_zero (225/16) (3675/256) (by norm_num) c0237

theorem c0238 : checkPiece pa19 (3675/256) 0 (3675/256) (1875/128) = true := by decide +kernel
theorem n0238 : NonnegOnQ (3675/256) (1875/128) :=
  nonnegOn_of_checkPiece_zero (3675/256) (1875/128) (by norm_num) c0238

theorem c0239 : checkPiece pa19 (1875/128) 0 (1875/128) (3825/256) = true := by decide +kernel
theorem n0239 : NonnegOnQ (1875/128) (3825/256) :=
  nonnegOn_of_checkPiece_zero (1875/128) (3825/256) (by norm_num) c0239

theorem c0240 : checkPiece pa19 (3825/256) 0 (3825/256) (975/64) = true := by decide +kernel
theorem n0240 : NonnegOnQ (3825/256) (975/64) :=
  nonnegOn_of_checkPiece_zero (3825/256) (975/64) (by norm_num) c0240

theorem c0241 : checkPiece pa19 (975/64) 0 (975/64) (3975/256) = true := by decide +kernel
theorem n0241 : NonnegOnQ (975/64) (3975/256) :=
  nonnegOn_of_checkPiece_zero (975/64) (3975/256) (by norm_num) c0241

theorem c0242 : checkPiece pa19 (3975/256) 0 (3975/256) (2025/128) = true := by decide +kernel
theorem n0242 : NonnegOnQ (3975/256) (2025/128) :=
  nonnegOn_of_checkPiece_zero (3975/256) (2025/128) (by norm_num) c0242

theorem c0243 : checkPiece pa19 (2025/128) 0 (2025/128) (4125/256) = true := by decide +kernel
theorem n0243 : NonnegOnQ (2025/128) (4125/256) :=
  nonnegOn_of_checkPiece_zero (2025/128) (4125/256) (by norm_num) c0243

theorem c0244 : checkPiece pa19 (4125/256) 0 (4125/256) (8325/512) = true := by decide +kernel
theorem n0244 : NonnegOnQ (4125/256) (8325/512) :=
  nonnegOn_of_checkPiece_zero (4125/256) (8325/512) (by norm_num) c0244

theorem c0245 : checkPiece pa19 (8325/512) 0 (8325/512) (525/32) = true := by decide +kernel
theorem n0245 : NonnegOnQ (8325/512) (525/32) :=
  nonnegOn_of_checkPiece_zero (8325/512) (525/32) (by norm_num) c0245

theorem c0246 : checkPiece pa19 (525/32) 0 (525/32) (4275/256) = true := by decide +kernel
theorem n0246 : NonnegOnQ (525/32) (4275/256) :=
  nonnegOn_of_checkPiece_zero (525/32) (4275/256) (by norm_num) c0246

theorem c0247 : checkPiece pa19 (4275/256) 0 (4275/256) (2175/128) = true := by decide +kernel
theorem n0247 : NonnegOnQ (4275/256) (2175/128) :=
  nonnegOn_of_checkPiece_zero (4275/256) (2175/128) (by norm_num) c0247

theorem c0248 : checkPiece pa19 (2175/128) 0 (2175/128) (4425/256) = true := by decide +kernel
theorem n0248 : NonnegOnQ (2175/128) (4425/256) :=
  nonnegOn_of_checkPiece_zero (2175/128) (4425/256) (by norm_num) c0248

theorem c0249 : checkPiece pa19 (4425/256) 0 (4425/256) (1125/64) = true := by decide +kernel
theorem n0249 : NonnegOnQ (4425/256) (1125/64) :=
  nonnegOn_of_checkPiece_zero (4425/256) (1125/64) (by norm_num) c0249

theorem c0250 : checkPiece pa19 (1125/64) 0 (1125/64) (4575/256) = true := by decide +kernel
theorem n0250 : NonnegOnQ (1125/64) (4575/256) :=
  nonnegOn_of_checkPiece_zero (1125/64) (4575/256) (by norm_num) c0250

theorem c0251 : checkPiece pa19 (4575/256) 0 (4575/256) (2325/128) = true := by decide +kernel
theorem n0251 : NonnegOnQ (4575/256) (2325/128) :=
  nonnegOn_of_checkPiece_zero (4575/256) (2325/128) (by norm_num) c0251

theorem c0252 : checkPiece pa19 (2325/128) 0 (2325/128) (4725/256) = true := by decide +kernel
theorem n0252 : NonnegOnQ (2325/128) (4725/256) :=
  nonnegOn_of_checkPiece_zero (2325/128) (4725/256) (by norm_num) c0252

theorem c0253 : checkPiece pa19 (4725/256) 0 (4725/256) (75/4) = true := by decide +kernel
theorem n0253 : NonnegOnQ (4725/256) (75/4) :=
  nonnegOn_of_checkPiece_zero (4725/256) (75/4) (by norm_num) c0253

theorem c0254 : checkPiece pa19 (75/4) 0 (75/4) (4875/256) = true := by decide +kernel
theorem n0254 : NonnegOnQ (75/4) (4875/256) :=
  nonnegOn_of_checkPiece_zero (75/4) (4875/256) (by norm_num) c0254

theorem c0255 : checkPiece pa19 (4875/256) 0 (4875/256) (2475/128) = true := by decide +kernel
theorem n0255 : NonnegOnQ (4875/256) (2475/128) :=
  nonnegOn_of_checkPiece_zero (4875/256) (2475/128) (by norm_num) c0255

theorem c0256 : checkPiece pa19 (2475/128) 0 (2475/128) (5025/256) = true := by decide +kernel
theorem n0256 : NonnegOnQ (2475/128) (5025/256) :=
  nonnegOn_of_checkPiece_zero (2475/128) (5025/256) (by norm_num) c0256

theorem c0257 : checkPiece pa19 (5025/256) 0 (5025/256) (1275/64) = true := by decide +kernel
theorem n0257 : NonnegOnQ (5025/256) (1275/64) :=
  nonnegOn_of_checkPiece_zero (5025/256) (1275/64) (by norm_num) c0257

theorem c0258 : checkPiece pa19 (1275/64) 0 (1275/64) (5175/256) = true := by decide +kernel
theorem n0258 : NonnegOnQ (1275/64) (5175/256) :=
  nonnegOn_of_checkPiece_zero (1275/64) (5175/256) (by norm_num) c0258

theorem c0259 : checkPiece pa19 (5175/256) 0 (5175/256) (10425/512) = true := by decide +kernel
theorem n0259 : NonnegOnQ (5175/256) (10425/512) :=
  nonnegOn_of_checkPiece_zero (5175/256) (10425/512) (by norm_num) c0259

theorem c0260 : checkPiece pa19 (10425/512) 0 (10425/512) (2625/128) = true := by decide +kernel
theorem n0260 : NonnegOnQ (10425/512) (2625/128) :=
  nonnegOn_of_checkPiece_zero (10425/512) (2625/128) (by norm_num) c0260

theorem c0261 : checkPiece pa19 (2625/128) 0 (2625/128) (5325/256) = true := by decide +kernel
theorem n0261 : NonnegOnQ (2625/128) (5325/256) :=
  nonnegOn_of_checkPiece_zero (2625/128) (5325/256) (by norm_num) c0261

theorem c0262 : checkPiece pa19 (5325/256) 0 (5325/256) (675/32) = true := by decide +kernel
theorem n0262 : NonnegOnQ (5325/256) (675/32) :=
  nonnegOn_of_checkPiece_zero (5325/256) (675/32) (by norm_num) c0262

theorem c0263 : checkPiece pa19 (675/32) 0 (675/32) (2775/128) = true := by decide +kernel
theorem n0263 : NonnegOnQ (675/32) (2775/128) :=
  nonnegOn_of_checkPiece_zero (675/32) (2775/128) (by norm_num) c0263

theorem c0264 : checkPiece pa19 (2775/128) 0 (2775/128) (1425/64) = true := by decide +kernel
theorem n0264 : NonnegOnQ (2775/128) (1425/64) :=
  nonnegOn_of_checkPiece_zero (2775/128) (1425/64) (by norm_num) c0264

theorem c0265 : checkPiece pa19 (1425/64) 0 (1425/64) (375/16) = true := by decide +kernel
theorem n0265 : NonnegOnQ (1425/64) (375/16) :=
  nonnegOn_of_checkPiece_zero (1425/64) (375/16) (by norm_num) c0265

theorem c0266 : checkPiece pa19 (375/16) 0 (375/16) (1575/64) = true := by decide +kernel
theorem n0266 : NonnegOnQ (375/16) (1575/64) :=
  nonnegOn_of_checkPiece_zero (375/16) (1575/64) (by norm_num) c0266

theorem c0267 : checkPiece pa19 (1575/64) 0 (1575/64) (3225/128) = true := by decide +kernel
theorem n0267 : NonnegOnQ (1575/64) (3225/128) :=
  nonnegOn_of_checkPiece_zero (1575/64) (3225/128) (by norm_num) c0267

theorem c0268 : checkPiece pa19 (3225/128) 0 (3225/128) (6525/256) = true := by decide +kernel
theorem n0268 : NonnegOnQ (3225/128) (6525/256) :=
  nonnegOn_of_checkPiece_zero (3225/128) (6525/256) (by norm_num) c0268

theorem c0269 : checkPiece pa19 (6525/256) 0 (6525/256) (825/32) = true := by decide +kernel
theorem n0269 : NonnegOnQ (6525/256) (825/32) :=
  nonnegOn_of_checkPiece_zero (6525/256) (825/32) (by norm_num) c0269

theorem c0270 : checkPiece pa19 (825/32) 0 (825/32) (6675/256) = true := by decide +kernel
theorem n0270 : NonnegOnQ (825/32) (6675/256) :=
  nonnegOn_of_checkPiece_zero (825/32) (6675/256) (by norm_num) c0270

theorem c0271 : checkPiece pa19 (6675/256) 0 (6675/256) (13425/512) = true := by decide +kernel
theorem n0271 : NonnegOnQ (6675/256) (13425/512) :=
  nonnegOn_of_checkPiece_zero (6675/256) (13425/512) (by norm_num) c0271

theorem c0272 : checkPiece pa19 (13425/512) 0 (13425/512) (3375/128) = true := by decide +kernel
theorem n0272 : NonnegOnQ (13425/512) (3375/128) :=
  nonnegOn_of_checkPiece_zero (13425/512) (3375/128) (by norm_num) c0272

theorem c0273 : checkPiece pa19 (3375/128) 0 (3375/128) (6825/256) = true := by decide +kernel
theorem n0273 : NonnegOnQ (3375/128) (6825/256) :=
  nonnegOn_of_checkPiece_zero (3375/128) (6825/256) (by norm_num) c0273

theorem c0274 : checkPiece pa19 (6825/256) 0 (6825/256) (1725/64) = true := by decide +kernel
theorem n0274 : NonnegOnQ (6825/256) (1725/64) :=
  nonnegOn_of_checkPiece_zero (6825/256) (1725/64) (by norm_num) c0274

theorem c0275 : checkPiece pa19 (1725/64) 0 (1725/64) (6975/256) = true := by decide +kernel
theorem n0275 : NonnegOnQ (1725/64) (6975/256) :=
  nonnegOn_of_checkPiece_zero (1725/64) (6975/256) (by norm_num) c0275

theorem c0276 : checkPiece pa19 (6975/256) 0 (6975/256) (3525/128) = true := by decide +kernel
theorem n0276 : NonnegOnQ (6975/256) (3525/128) :=
  nonnegOn_of_checkPiece_zero (6975/256) (3525/128) (by norm_num) c0276

theorem c0277 : checkPiece pa19 (3525/128) 0 (3525/128) (7125/256) = true := by decide +kernel
theorem n0277 : NonnegOnQ (3525/128) (7125/256) :=
  nonnegOn_of_checkPiece_zero (3525/128) (7125/256) (by norm_num) c0277

theorem c0278 : checkPiece pa19 (7125/256) 0 (7125/256) (225/8) = true := by decide +kernel
theorem n0278 : NonnegOnQ (7125/256) (225/8) :=
  nonnegOn_of_checkPiece_zero (7125/256) (225/8) (by norm_num) c0278

theorem c0279 : checkPiece pa19 (225/8) 0 (225/8) (7275/256) = true := by decide +kernel
theorem n0279 : NonnegOnQ (225/8) (7275/256) :=
  nonnegOn_of_checkPiece_zero (225/8) (7275/256) (by norm_num) c0279

theorem c0280 : checkPiece pa19 (7275/256) 0 (7275/256) (3675/128) = true := by decide +kernel
theorem n0280 : NonnegOnQ (7275/256) (3675/128) :=
  nonnegOn_of_checkPiece_zero (7275/256) (3675/128) (by norm_num) c0280

theorem c0281 : checkPiece pa19 (3675/128) 0 (3675/128) (7425/256) = true := by decide +kernel
theorem n0281 : NonnegOnQ (3675/128) (7425/256) :=
  nonnegOn_of_checkPiece_zero (3675/128) (7425/256) (by norm_num) c0281

theorem c0282 : checkPiece pa19 (7425/256) 0 (7425/256) (1875/64) = true := by decide +kernel
theorem n0282 : NonnegOnQ (7425/256) (1875/64) :=
  nonnegOn_of_checkPiece_zero (7425/256) (1875/64) (by norm_num) c0282

theorem c0283 : checkPiece pa19 (1875/64) 0 (1875/64) (975/32) = true := by decide +kernel
theorem n0283 : NonnegOnQ (1875/64) (975/32) :=
  nonnegOn_of_checkPiece_zero (1875/64) (975/32) (by norm_num) c0283

/- Original contiguous interval fold, staged to bound Lean memory use. -/
set_option maxRecDepth 4096 in
theorem foldTo0283 : NonnegOnQ 0 (975/32) := by
  have h236 := foldTo0236
  have h237 : NonnegOnQ 0 (3675/256) := nonnegOn_union 0 (225/16) (3675/256) h236 n0237
  have h238 : NonnegOnQ 0 (1875/128) := nonnegOn_union 0 (3675/256) (1875/128) h237 n0238
  have h239 : NonnegOnQ 0 (3825/256) := nonnegOn_union 0 (1875/128) (3825/256) h238 n0239
  have h240 : NonnegOnQ 0 (975/64) := nonnegOn_union 0 (3825/256) (975/64) h239 n0240
  have h241 : NonnegOnQ 0 (3975/256) := nonnegOn_union 0 (975/64) (3975/256) h240 n0241
  have h242 : NonnegOnQ 0 (2025/128) := nonnegOn_union 0 (3975/256) (2025/128) h241 n0242
  have h243 : NonnegOnQ 0 (4125/256) := nonnegOn_union 0 (2025/128) (4125/256) h242 n0243
  have h244 : NonnegOnQ 0 (8325/512) := nonnegOn_union 0 (4125/256) (8325/512) h243 n0244
  have h245 : NonnegOnQ 0 (525/32) := nonnegOn_union 0 (8325/512) (525/32) h244 n0245
  have h246 : NonnegOnQ 0 (4275/256) := nonnegOn_union 0 (525/32) (4275/256) h245 n0246
  have h247 : NonnegOnQ 0 (2175/128) := nonnegOn_union 0 (4275/256) (2175/128) h246 n0247
  have h248 : NonnegOnQ 0 (4425/256) := nonnegOn_union 0 (2175/128) (4425/256) h247 n0248
  have h249 : NonnegOnQ 0 (1125/64) := nonnegOn_union 0 (4425/256) (1125/64) h248 n0249
  have h250 : NonnegOnQ 0 (4575/256) := nonnegOn_union 0 (1125/64) (4575/256) h249 n0250
  have h251 : NonnegOnQ 0 (2325/128) := nonnegOn_union 0 (4575/256) (2325/128) h250 n0251
  have h252 : NonnegOnQ 0 (4725/256) := nonnegOn_union 0 (2325/128) (4725/256) h251 n0252
  have h253 : NonnegOnQ 0 (75/4) := nonnegOn_union 0 (4725/256) (75/4) h252 n0253
  have h254 : NonnegOnQ 0 (4875/256) := nonnegOn_union 0 (75/4) (4875/256) h253 n0254
  have h255 : NonnegOnQ 0 (2475/128) := nonnegOn_union 0 (4875/256) (2475/128) h254 n0255
  have h256 : NonnegOnQ 0 (5025/256) := nonnegOn_union 0 (2475/128) (5025/256) h255 n0256
  have h257 : NonnegOnQ 0 (1275/64) := nonnegOn_union 0 (5025/256) (1275/64) h256 n0257
  have h258 : NonnegOnQ 0 (5175/256) := nonnegOn_union 0 (1275/64) (5175/256) h257 n0258
  have h259 : NonnegOnQ 0 (10425/512) := nonnegOn_union 0 (5175/256) (10425/512) h258 n0259
  have h260 : NonnegOnQ 0 (2625/128) := nonnegOn_union 0 (10425/512) (2625/128) h259 n0260
  have h261 : NonnegOnQ 0 (5325/256) := nonnegOn_union 0 (2625/128) (5325/256) h260 n0261
  have h262 : NonnegOnQ 0 (675/32) := nonnegOn_union 0 (5325/256) (675/32) h261 n0262
  have h263 : NonnegOnQ 0 (2775/128) := nonnegOn_union 0 (675/32) (2775/128) h262 n0263
  have h264 : NonnegOnQ 0 (1425/64) := nonnegOn_union 0 (2775/128) (1425/64) h263 n0264
  have h265 : NonnegOnQ 0 (375/16) := nonnegOn_union 0 (1425/64) (375/16) h264 n0265
  have h266 : NonnegOnQ 0 (1575/64) := nonnegOn_union 0 (375/16) (1575/64) h265 n0266
  have h267 : NonnegOnQ 0 (3225/128) := nonnegOn_union 0 (1575/64) (3225/128) h266 n0267
  have h268 : NonnegOnQ 0 (6525/256) := nonnegOn_union 0 (3225/128) (6525/256) h267 n0268
  have h269 : NonnegOnQ 0 (825/32) := nonnegOn_union 0 (6525/256) (825/32) h268 n0269
  have h270 : NonnegOnQ 0 (6675/256) := nonnegOn_union 0 (825/32) (6675/256) h269 n0270
  have h271 : NonnegOnQ 0 (13425/512) := nonnegOn_union 0 (6675/256) (13425/512) h270 n0271
  have h272 : NonnegOnQ 0 (3375/128) := nonnegOn_union 0 (13425/512) (3375/128) h271 n0272
  have h273 : NonnegOnQ 0 (6825/256) := nonnegOn_union 0 (3375/128) (6825/256) h272 n0273
  have h274 : NonnegOnQ 0 (1725/64) := nonnegOn_union 0 (6825/256) (1725/64) h273 n0274
  have h275 : NonnegOnQ 0 (6975/256) := nonnegOn_union 0 (1725/64) (6975/256) h274 n0275
  have h276 : NonnegOnQ 0 (3525/128) := nonnegOn_union 0 (6975/256) (3525/128) h275 n0276
  have h277 : NonnegOnQ 0 (7125/256) := nonnegOn_union 0 (3525/128) (7125/256) h276 n0277
  have h278 : NonnegOnQ 0 (225/8) := nonnegOn_union 0 (7125/256) (225/8) h277 n0278
  have h279 : NonnegOnQ 0 (7275/256) := nonnegOn_union 0 (225/8) (7275/256) h278 n0279
  have h280 : NonnegOnQ 0 (3675/128) := nonnegOn_union 0 (7275/256) (3675/128) h279 n0280
  have h281 : NonnegOnQ 0 (7425/256) := nonnegOn_union 0 (3675/128) (7425/256) h280 n0281
  have h282 : NonnegOnQ 0 (1875/64) := nonnegOn_union 0 (7425/256) (1875/64) h281 n0282
  have h283 : NonnegOnQ 0 (975/32) := nonnegOn_union 0 (1875/64) (975/32) h282 n0283
  exact h283

end AEGIS.RHKreinTrigramAdaptiveV1
