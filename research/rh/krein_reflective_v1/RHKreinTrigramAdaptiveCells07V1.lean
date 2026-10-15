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
import RHKreinTrigramAdaptiveCells06V1

set_option autoImplicit false
noncomputable section
namespace AEGIS.RHKreinTrigramAdaptiveV1
open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinCellBatchV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinFirstCellV1
open AEGIS.RHKreinSecondCellReductionV1

theorem c0284 : checkPiece pa19 (975/32) 0 (975/32) (525/16) = true := by decide +kernel
theorem n0284 : NonnegOnQ (975/32) (525/16) :=
  nonnegOn_of_checkPiece_zero (975/32) (525/16) (by norm_num) c0284

theorem c0285 : checkPiece pa19 (525/16) 0 (525/16) (2175/64) = true := by decide +kernel
theorem n0285 : NonnegOnQ (525/16) (2175/64) :=
  nonnegOn_of_checkPiece_zero (525/16) (2175/64) (by norm_num) c0285

theorem c0286 : checkPiece pa19 (2175/64) 0 (2175/64) (4425/128) = true := by decide +kernel
theorem n0286 : NonnegOnQ (2175/64) (4425/128) :=
  nonnegOn_of_checkPiece_zero (2175/64) (4425/128) (by norm_num) c0286

theorem c0287 : checkPiece pa19 (4425/128) 0 (4425/128) (8925/256) = true := by decide +kernel
theorem n0287 : NonnegOnQ (4425/128) (8925/256) :=
  nonnegOn_of_checkPiece_zero (4425/128) (8925/256) (by norm_num) c0287

theorem c0288 : checkPiece pa19 (8925/256) 0 (8925/256) (1125/32) = true := by decide +kernel
theorem n0288 : NonnegOnQ (8925/256) (1125/32) :=
  nonnegOn_of_checkPiece_zero (8925/256) (1125/32) (by norm_num) c0288

theorem c0289 : checkPiece pa19 (1125/32) 0 (1125/32) (9075/256) = true := by decide +kernel
theorem n0289 : NonnegOnQ (1125/32) (9075/256) :=
  nonnegOn_of_checkPiece_zero (1125/32) (9075/256) (by norm_num) c0289

theorem c0290 : checkPiece pa19 (9075/256) 0 (9075/256) (4575/128) = true := by decide +kernel
theorem n0290 : NonnegOnQ (9075/256) (4575/128) :=
  nonnegOn_of_checkPiece_zero (9075/256) (4575/128) (by norm_num) c0290

theorem c0291 : checkPiece pa19 (4575/128) 0 (4575/128) (9225/256) = true := by decide +kernel
theorem n0291 : NonnegOnQ (4575/128) (9225/256) :=
  nonnegOn_of_checkPiece_zero (4575/128) (9225/256) (by norm_num) c0291

theorem c0292 : checkPiece pa19 (9225/256) 0 (9225/256) (18525/512) = true := by decide +kernel
theorem n0292 : NonnegOnQ (9225/256) (18525/512) :=
  nonnegOn_of_checkPiece_zero (9225/256) (18525/512) (by norm_num) c0292

theorem c0293 : checkPiece pa19 (18525/512) 0 (18525/512) (2325/64) = true := by decide +kernel
theorem n0293 : NonnegOnQ (18525/512) (2325/64) :=
  nonnegOn_of_checkPiece_zero (18525/512) (2325/64) (by norm_num) c0293

theorem c0294 : checkPiece pa19 (2325/64) 0 (2325/64) (9375/256) = true := by decide +kernel
theorem n0294 : NonnegOnQ (2325/64) (9375/256) :=
  nonnegOn_of_checkPiece_zero (2325/64) (9375/256) (by norm_num) c0294

theorem c0295 : checkPiece pa19 (9375/256) 0 (9375/256) (4725/128) = true := by decide +kernel
theorem n0295 : NonnegOnQ (9375/256) (4725/128) :=
  nonnegOn_of_checkPiece_zero (9375/256) (4725/128) (by norm_num) c0295

theorem c0296 : checkPiece pa19 (4725/128) 0 (4725/128) (75/2) = true := by decide +kernel
theorem n0296 : NonnegOnQ (4725/128) (75/2) :=
  nonnegOn_of_checkPiece_zero (4725/128) (75/2) (by norm_num) c0296

theorem c0297 : checkPiece pa19 (75/2) 0 (75/2) (1275/32) = true := by decide +kernel
theorem n0297 : NonnegOnQ (75/2) (1275/32) :=
  nonnegOn_of_checkPiece_zero (75/2) (1275/32) (by norm_num) c0297

theorem c0298 : checkPiece pa19 (1275/32) 0 (1275/32) (675/16) = true := by decide +kernel
theorem n0298 : NonnegOnQ (1275/32) (675/16) :=
  nonnegOn_of_checkPiece_zero (1275/32) (675/16) (by norm_num) c0298

theorem c0299 : checkPiece pa19 (675/16) 0 (675/16) (2775/64) = true := by decide +kernel
theorem n0299 : NonnegOnQ (675/16) (2775/64) :=
  nonnegOn_of_checkPiece_zero (675/16) (2775/64) (by norm_num) c0299

theorem c0300 : checkPiece pa19 (2775/64) 0 (2775/64) (1425/32) = true := by decide +kernel
theorem n0300 : NonnegOnQ (2775/64) (1425/32) :=
  nonnegOn_of_checkPiece_zero (2775/64) (1425/32) (by norm_num) c0300

theorem c0301 : checkPiece pa19 (1425/32) 0 (1425/32) (2925/64) = true := by decide +kernel
theorem n0301 : NonnegOnQ (1425/32) (2925/64) :=
  nonnegOn_of_checkPiece_zero (1425/32) (2925/64) (by norm_num) c0301

theorem c0302 : checkPiece pa19 (2925/64) 0 (2925/64) (375/8) = true := by decide +kernel
theorem n0302 : NonnegOnQ (2925/64) (375/8) :=
  nonnegOn_of_checkPiece_zero (2925/64) (375/8) (by norm_num) c0302

theorem c0303 : checkPiece pa19 (375/8) 0 (375/8) (1575/32) = true := by decide +kernel
theorem n0303 : NonnegOnQ (375/8) (1575/32) :=
  nonnegOn_of_checkPiece_zero (375/8) (1575/32) (by norm_num) c0303

theorem c0304 : checkPiece pa19 (1575/32) 0 (1575/32) (825/16) = true := by decide +kernel
theorem n0304 : NonnegOnQ (1575/32) (825/16) :=
  nonnegOn_of_checkPiece_zero (1575/32) (825/16) (by norm_num) c0304

theorem c0305 : checkPiece pa19 (825/16) 0 (825/16) (1725/32) = true := by decide +kernel
theorem n0305 : NonnegOnQ (825/16) (1725/32) :=
  nonnegOn_of_checkPiece_zero (825/16) (1725/32) (by norm_num) c0305

theorem c0306 : checkPiece pa19 (1725/32) 0 (1725/32) (225/4) = true := by decide +kernel
theorem n0306 : NonnegOnQ (1725/32) (225/4) :=
  nonnegOn_of_checkPiece_zero (1725/32) (225/4) (by norm_num) c0306

theorem c0307 : checkPiece pa19 (225/4) 0 (225/4) (1875/32) = true := by decide +kernel
theorem n0307 : NonnegOnQ (225/4) (1875/32) :=
  nonnegOn_of_checkPiece_zero (225/4) (1875/32) (by norm_num) c0307

theorem c0308 : checkPiece pa19 (1875/32) 0 (1875/32) (975/16) = true := by decide +kernel
theorem n0308 : NonnegOnQ (1875/32) (975/16) :=
  nonnegOn_of_checkPiece_zero (1875/32) (975/16) (by norm_num) c0308

theorem c0309 : checkPiece pa19 (975/16) 0 (975/16) (2025/32) = true := by decide +kernel
theorem n0309 : NonnegOnQ (975/16) (2025/32) :=
  nonnegOn_of_checkPiece_zero (975/16) (2025/32) (by norm_num) c0309

theorem c0310 : checkPiece pa19 (2025/32) 0 (2025/32) (525/8) = true := by decide +kernel
theorem n0310 : NonnegOnQ (2025/32) (525/8) :=
  nonnegOn_of_checkPiece_zero (2025/32) (525/8) (by norm_num) c0310

theorem c0311 : checkPiece pa19 (525/8) 0 (525/8) (2175/32) = true := by decide +kernel
theorem n0311 : NonnegOnQ (525/8) (2175/32) :=
  nonnegOn_of_checkPiece_zero (525/8) (2175/32) (by norm_num) c0311

theorem c0312 : checkPiece pa19 (2175/32) 0 (2175/32) (1125/16) = true := by decide +kernel
theorem n0312 : NonnegOnQ (2175/32) (1125/16) :=
  nonnegOn_of_checkPiece_zero (2175/32) (1125/16) (by norm_num) c0312

theorem c0313 : checkPiece pa19 (1125/16) 0 (1125/16) (2325/32) = true := by decide +kernel
theorem n0313 : NonnegOnQ (1125/16) (2325/32) :=
  nonnegOn_of_checkPiece_zero (1125/16) (2325/32) (by norm_num) c0313

theorem c0314 : checkPiece pa19 (2325/32) 0 (2325/32) (4725/64) = true := by decide +kernel
theorem n0314 : NonnegOnQ (2325/32) (4725/64) :=
  nonnegOn_of_checkPiece_zero (2325/32) (4725/64) (by norm_num) c0314

theorem c0315 : checkPiece pa19 (4725/64) 0 (4725/64) (75) = true := by decide +kernel
theorem n0315 : NonnegOnQ (4725/64) (75) :=
  nonnegOn_of_checkPiece_zero (4725/64) (75) (by norm_num) c0315

theorem c0316 : checkPiece pa19 (75) 0 (75) (2475/32) = true := by decide +kernel
theorem n0316 : NonnegOnQ (75) (2475/32) :=
  nonnegOn_of_checkPiece_zero (75) (2475/32) (by norm_num) c0316

theorem c0317 : checkPiece pa19 (2475/32) 0 (2475/32) (1275/16) = true := by decide +kernel
theorem n0317 : NonnegOnQ (2475/32) (1275/16) :=
  nonnegOn_of_checkPiece_zero (2475/32) (1275/16) (by norm_num) c0317

theorem c0318 : checkPiece pa19 (1275/16) 0 (1275/16) (5175/64) = true := by decide +kernel
theorem n0318 : NonnegOnQ (1275/16) (5175/64) :=
  nonnegOn_of_checkPiece_zero (1275/16) (5175/64) (by norm_num) c0318

theorem c0319 : checkPiece pa19 (5175/64) 0 (5175/64) (2625/32) = true := by decide +kernel
theorem n0319 : NonnegOnQ (5175/64) (2625/32) :=
  nonnegOn_of_checkPiece_zero (5175/64) (2625/32) (by norm_num) c0319

theorem c0320 : checkPiece pa19 (2625/32) 0 (2625/32) (5325/64) = true := by decide +kernel
theorem n0320 : NonnegOnQ (2625/32) (5325/64) :=
  nonnegOn_of_checkPiece_zero (2625/32) (5325/64) (by norm_num) c0320

theorem c0321 : checkPiece pa19 (5325/64) 0 (5325/64) (675/8) = true := by decide +kernel
theorem n0321 : NonnegOnQ (5325/64) (675/8) :=
  nonnegOn_of_checkPiece_zero (5325/64) (675/8) (by norm_num) c0321

theorem c0322 : checkPiece pa19 (675/8) 0 (675/8) (2775/32) = true := by decide +kernel
theorem n0322 : NonnegOnQ (675/8) (2775/32) :=
  nonnegOn_of_checkPiece_zero (675/8) (2775/32) (by norm_num) c0322

theorem c0323 : checkPiece pa19 (2775/32) 0 (2775/32) (1425/16) = true := by decide +kernel
theorem n0323 : NonnegOnQ (2775/32) (1425/16) :=
  nonnegOn_of_checkPiece_zero (2775/32) (1425/16) (by norm_num) c0323

theorem c0324 : checkPiece pa19 (1425/16) 0 (1425/16) (5775/64) = true := by decide +kernel
theorem n0324 : NonnegOnQ (1425/16) (5775/64) :=
  nonnegOn_of_checkPiece_zero (1425/16) (5775/64) (by norm_num) c0324

theorem c0325 : checkPiece pa19 (5775/64) 0 (5775/64) (2925/32) = true := by decide +kernel
theorem n0325 : NonnegOnQ (5775/64) (2925/32) :=
  nonnegOn_of_checkPiece_zero (5775/64) (2925/32) (by norm_num) c0325

theorem c0326 : checkPiece pa19 (2925/32) 0 (2925/32) (375/4) = true := by decide +kernel
theorem n0326 : NonnegOnQ (2925/32) (375/4) :=
  nonnegOn_of_checkPiece_zero (2925/32) (375/4) (by norm_num) c0326

theorem c0327 : checkPiece pa19 (375/4) 0 (375/4) (3075/32) = true := by decide +kernel
theorem n0327 : NonnegOnQ (375/4) (3075/32) :=
  nonnegOn_of_checkPiece_zero (375/4) (3075/32) (by norm_num) c0327

theorem c0328 : checkPiece pa19 (3075/32) 0 (3075/32) (1575/16) = true := by decide +kernel
theorem n0328 : NonnegOnQ (3075/32) (1575/16) :=
  nonnegOn_of_checkPiece_zero (3075/32) (1575/16) (by norm_num) c0328

theorem c0329 : checkPiece pa19 (1575/16) 0 (1575/16) (3225/32) = true := by decide +kernel
theorem n0329 : NonnegOnQ (1575/16) (3225/32) :=
  nonnegOn_of_checkPiece_zero (1575/16) (3225/32) (by norm_num) c0329

theorem c0330 : checkPiece pa19 (3225/32) 0 (3225/32) (825/8) = true := by decide +kernel
theorem n0330 : NonnegOnQ (3225/32) (825/8) :=
  nonnegOn_of_checkPiece_zero (3225/32) (825/8) (by norm_num) c0330

/- Original contiguous interval fold, staged to bound Lean memory use. -/
set_option maxRecDepth 4096 in
theorem foldTo0330 : NonnegOnQ 0 (825/8) := by
  have h283 := foldTo0283
  have h284 : NonnegOnQ 0 (525/16) := nonnegOn_union 0 (975/32) (525/16) h283 n0284
  have h285 : NonnegOnQ 0 (2175/64) := nonnegOn_union 0 (525/16) (2175/64) h284 n0285
  have h286 : NonnegOnQ 0 (4425/128) := nonnegOn_union 0 (2175/64) (4425/128) h285 n0286
  have h287 : NonnegOnQ 0 (8925/256) := nonnegOn_union 0 (4425/128) (8925/256) h286 n0287
  have h288 : NonnegOnQ 0 (1125/32) := nonnegOn_union 0 (8925/256) (1125/32) h287 n0288
  have h289 : NonnegOnQ 0 (9075/256) := nonnegOn_union 0 (1125/32) (9075/256) h288 n0289
  have h290 : NonnegOnQ 0 (4575/128) := nonnegOn_union 0 (9075/256) (4575/128) h289 n0290
  have h291 : NonnegOnQ 0 (9225/256) := nonnegOn_union 0 (4575/128) (9225/256) h290 n0291
  have h292 : NonnegOnQ 0 (18525/512) := nonnegOn_union 0 (9225/256) (18525/512) h291 n0292
  have h293 : NonnegOnQ 0 (2325/64) := nonnegOn_union 0 (18525/512) (2325/64) h292 n0293
  have h294 : NonnegOnQ 0 (9375/256) := nonnegOn_union 0 (2325/64) (9375/256) h293 n0294
  have h295 : NonnegOnQ 0 (4725/128) := nonnegOn_union 0 (9375/256) (4725/128) h294 n0295
  have h296 : NonnegOnQ 0 (75/2) := nonnegOn_union 0 (4725/128) (75/2) h295 n0296
  have h297 : NonnegOnQ 0 (1275/32) := nonnegOn_union 0 (75/2) (1275/32) h296 n0297
  have h298 : NonnegOnQ 0 (675/16) := nonnegOn_union 0 (1275/32) (675/16) h297 n0298
  have h299 : NonnegOnQ 0 (2775/64) := nonnegOn_union 0 (675/16) (2775/64) h298 n0299
  have h300 : NonnegOnQ 0 (1425/32) := nonnegOn_union 0 (2775/64) (1425/32) h299 n0300
  have h301 : NonnegOnQ 0 (2925/64) := nonnegOn_union 0 (1425/32) (2925/64) h300 n0301
  have h302 : NonnegOnQ 0 (375/8) := nonnegOn_union 0 (2925/64) (375/8) h301 n0302
  have h303 : NonnegOnQ 0 (1575/32) := nonnegOn_union 0 (375/8) (1575/32) h302 n0303
  have h304 : NonnegOnQ 0 (825/16) := nonnegOn_union 0 (1575/32) (825/16) h303 n0304
  have h305 : NonnegOnQ 0 (1725/32) := nonnegOn_union 0 (825/16) (1725/32) h304 n0305
  have h306 : NonnegOnQ 0 (225/4) := nonnegOn_union 0 (1725/32) (225/4) h305 n0306
  have h307 : NonnegOnQ 0 (1875/32) := nonnegOn_union 0 (225/4) (1875/32) h306 n0307
  have h308 : NonnegOnQ 0 (975/16) := nonnegOn_union 0 (1875/32) (975/16) h307 n0308
  have h309 : NonnegOnQ 0 (2025/32) := nonnegOn_union 0 (975/16) (2025/32) h308 n0309
  have h310 : NonnegOnQ 0 (525/8) := nonnegOn_union 0 (2025/32) (525/8) h309 n0310
  have h311 : NonnegOnQ 0 (2175/32) := nonnegOn_union 0 (525/8) (2175/32) h310 n0311
  have h312 : NonnegOnQ 0 (1125/16) := nonnegOn_union 0 (2175/32) (1125/16) h311 n0312
  have h313 : NonnegOnQ 0 (2325/32) := nonnegOn_union 0 (1125/16) (2325/32) h312 n0313
  have h314 : NonnegOnQ 0 (4725/64) := nonnegOn_union 0 (2325/32) (4725/64) h313 n0314
  have h315 : NonnegOnQ 0 (75) := nonnegOn_union 0 (4725/64) (75) h314 n0315
  have h316 : NonnegOnQ 0 (2475/32) := nonnegOn_union 0 (75) (2475/32) h315 n0316
  have h317 : NonnegOnQ 0 (1275/16) := nonnegOn_union 0 (2475/32) (1275/16) h316 n0317
  have h318 : NonnegOnQ 0 (5175/64) := nonnegOn_union 0 (1275/16) (5175/64) h317 n0318
  have h319 : NonnegOnQ 0 (2625/32) := nonnegOn_union 0 (5175/64) (2625/32) h318 n0319
  have h320 : NonnegOnQ 0 (5325/64) := nonnegOn_union 0 (2625/32) (5325/64) h319 n0320
  have h321 : NonnegOnQ 0 (675/8) := nonnegOn_union 0 (5325/64) (675/8) h320 n0321
  have h322 : NonnegOnQ 0 (2775/32) := nonnegOn_union 0 (675/8) (2775/32) h321 n0322
  have h323 : NonnegOnQ 0 (1425/16) := nonnegOn_union 0 (2775/32) (1425/16) h322 n0323
  have h324 : NonnegOnQ 0 (5775/64) := nonnegOn_union 0 (1425/16) (5775/64) h323 n0324
  have h325 : NonnegOnQ 0 (2925/32) := nonnegOn_union 0 (5775/64) (2925/32) h324 n0325
  have h326 : NonnegOnQ 0 (375/4) := nonnegOn_union 0 (2925/32) (375/4) h325 n0326
  have h327 : NonnegOnQ 0 (3075/32) := nonnegOn_union 0 (375/4) (3075/32) h326 n0327
  have h328 : NonnegOnQ 0 (1575/16) := nonnegOn_union 0 (3075/32) (1575/16) h327 n0328
  have h329 : NonnegOnQ 0 (3225/32) := nonnegOn_union 0 (1575/16) (3225/32) h328 n0329
  have h330 : NonnegOnQ 0 (825/8) := nonnegOn_union 0 (3225/32) (825/8) h329 n0330
  exact h330

end AEGIS.RHKreinTrigramAdaptiveV1
