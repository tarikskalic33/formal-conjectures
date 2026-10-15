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
import RHKreinTrigramAdaptiveCells07V1

set_option autoImplicit false
noncomputable section
namespace AEGIS.RHKreinTrigramAdaptiveV1
open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinCellBatchV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinFirstCellV1
open AEGIS.RHKreinSecondCellReductionV1

theorem c0331 : checkPiece pa19 (825/8) 0 (825/8) (3375/32) = true := by decide +kernel
theorem n0331 : NonnegOnQ (825/8) (3375/32) :=
  nonnegOn_of_checkPiece_zero (825/8) (3375/32) (by norm_num) c0331

theorem c0332 : checkPiece pa19 (3375/32) 0 (3375/32) (1725/16) = true := by decide +kernel
theorem n0332 : NonnegOnQ (3375/32) (1725/16) :=
  nonnegOn_of_checkPiece_zero (3375/32) (1725/16) (by norm_num) c0332

theorem c0333 : checkPiece pa19 (1725/16) 0 (1725/16) (3525/32) = true := by decide +kernel
theorem n0333 : NonnegOnQ (1725/16) (3525/32) :=
  nonnegOn_of_checkPiece_zero (1725/16) (3525/32) (by norm_num) c0333

theorem c0334 : checkPiece pa19 (3525/32) 0 (3525/32) (225/2) = true := by decide +kernel
theorem n0334 : NonnegOnQ (3525/32) (225/2) :=
  nonnegOn_of_checkPiece_zero (3525/32) (225/2) (by norm_num) c0334

theorem c0335 : checkPiece pa19 (225/2) 0 (225/2) (3675/32) = true := by decide +kernel
theorem n0335 : NonnegOnQ (225/2) (3675/32) :=
  nonnegOn_of_checkPiece_zero (225/2) (3675/32) (by norm_num) c0335

theorem c0336 : checkPiece pa19 (3675/32) 0 (3675/32) (1875/16) = true := by decide +kernel
theorem n0336 : NonnegOnQ (3675/32) (1875/16) :=
  nonnegOn_of_checkPiece_zero (3675/32) (1875/16) (by norm_num) c0336

theorem c0337 : checkPiece pa19 (1875/16) 0 (1875/16) (3825/32) = true := by decide +kernel
theorem n0337 : NonnegOnQ (1875/16) (3825/32) :=
  nonnegOn_of_checkPiece_zero (1875/16) (3825/32) (by norm_num) c0337

theorem c0338 : checkPiece pa19 (3825/32) 0 (3825/32) (975/8) = true := by decide +kernel
theorem n0338 : NonnegOnQ (3825/32) (975/8) :=
  nonnegOn_of_checkPiece_zero (3825/32) (975/8) (by norm_num) c0338

theorem c0339 : checkPiece pa19 (975/8) 0 (975/8) (2025/16) = true := by decide +kernel
theorem n0339 : NonnegOnQ (975/8) (2025/16) :=
  nonnegOn_of_checkPiece_zero (975/8) (2025/16) (by norm_num) c0339

theorem c0340 : checkPiece pa19 (2025/16) 0 (2025/16) (4125/32) = true := by decide +kernel
theorem n0340 : NonnegOnQ (2025/16) (4125/32) :=
  nonnegOn_of_checkPiece_zero (2025/16) (4125/32) (by norm_num) c0340

theorem c0341 : checkPiece pa19 (4125/32) 0 (4125/32) (525/4) = true := by decide +kernel
theorem n0341 : NonnegOnQ (4125/32) (525/4) :=
  nonnegOn_of_checkPiece_zero (4125/32) (525/4) (by norm_num) c0341

theorem c0342 : checkPiece pa19 (525/4) 0 (525/4) (4275/32) = true := by decide +kernel
theorem n0342 : NonnegOnQ (525/4) (4275/32) :=
  nonnegOn_of_checkPiece_zero (525/4) (4275/32) (by norm_num) c0342

theorem c0343 : checkPiece pa19 (4275/32) 0 (4275/32) (8625/64) = true := by decide +kernel
theorem n0343 : NonnegOnQ (4275/32) (8625/64) :=
  nonnegOn_of_checkPiece_zero (4275/32) (8625/64) (by norm_num) c0343

theorem c0344 : checkPiece pa19 (8625/64) 0 (8625/64) (2175/16) = true := by decide +kernel
theorem n0344 : NonnegOnQ (8625/64) (2175/16) :=
  nonnegOn_of_checkPiece_zero (8625/64) (2175/16) (by norm_num) c0344

theorem c0345 : checkPiece pa19 (2175/16) 0 (2175/16) (8775/64) = true := by decide +kernel
theorem n0345 : NonnegOnQ (2175/16) (8775/64) :=
  nonnegOn_of_checkPiece_zero (2175/16) (8775/64) (by norm_num) c0345

theorem c0346 : checkPiece pa19 (8775/64) 0 (8775/64) (4425/32) = true := by decide +kernel
theorem n0346 : NonnegOnQ (8775/64) (4425/32) :=
  nonnegOn_of_checkPiece_zero (8775/64) (4425/32) (by norm_num) c0346

theorem c0347 : checkPiece pa19 (4425/32) 0 (4425/32) (1125/8) = true := by decide +kernel
theorem n0347 : NonnegOnQ (4425/32) (1125/8) :=
  nonnegOn_of_checkPiece_zero (4425/32) (1125/8) (by norm_num) c0347

theorem c0348 : checkPiece pa19 (1125/8) 0 (1125/8) (2325/16) = true := by decide +kernel
theorem n0348 : NonnegOnQ (1125/8) (2325/16) :=
  nonnegOn_of_checkPiece_zero (1125/8) (2325/16) (by norm_num) c0348

theorem c0349 : checkPiece pa19 (2325/16) 0 (2325/16) (150) = true := by decide +kernel
theorem n0349 : NonnegOnQ (2325/16) (150) :=
  nonnegOn_of_checkPiece_zero (2325/16) (150) (by norm_num) c0349

theorem c0350 : checkPiece pa19 (150) 0 (150) (4875/32) = true := by decide +kernel
theorem n0350 : NonnegOnQ (150) (4875/32) :=
  nonnegOn_of_checkPiece_zero (150) (4875/32) (by norm_num) c0350

theorem c0351 : checkPiece pa19 (4875/32) 0 (4875/32) (2475/16) = true := by decide +kernel
theorem n0351 : NonnegOnQ (4875/32) (2475/16) :=
  nonnegOn_of_checkPiece_zero (4875/32) (2475/16) (by norm_num) c0351

theorem c0352 : checkPiece pa19 (2475/16) 0 (2475/16) (1275/8) = true := by decide +kernel
theorem n0352 : NonnegOnQ (2475/16) (1275/8) :=
  nonnegOn_of_checkPiece_zero (2475/16) (1275/8) (by norm_num) c0352

theorem c0353 : checkPiece pa19 (1275/8) 0 (1275/8) (5175/32) = true := by decide +kernel
theorem n0353 : NonnegOnQ (1275/8) (5175/32) :=
  nonnegOn_of_checkPiece_zero (1275/8) (5175/32) (by norm_num) c0353

theorem c0354 : checkPiece pa19 (5175/32) 0 (5175/32) (2625/16) = true := by decide +kernel
theorem n0354 : NonnegOnQ (5175/32) (2625/16) :=
  nonnegOn_of_checkPiece_zero (5175/32) (2625/16) (by norm_num) c0354

theorem c0355 : checkPiece pa19 (2625/16) 0 (2625/16) (5325/32) = true := by decide +kernel
theorem n0355 : NonnegOnQ (2625/16) (5325/32) :=
  nonnegOn_of_checkPiece_zero (2625/16) (5325/32) (by norm_num) c0355

theorem c0356 : checkPiece pa19 (5325/32) 0 (5325/32) (675/4) = true := by decide +kernel
theorem n0356 : NonnegOnQ (5325/32) (675/4) :=
  nonnegOn_of_checkPiece_zero (5325/32) (675/4) (by norm_num) c0356

theorem c0357 : checkPiece pa19 (675/4) 0 (675/4) (2775/16) = true := by decide +kernel
theorem n0357 : NonnegOnQ (675/4) (2775/16) :=
  nonnegOn_of_checkPiece_zero (675/4) (2775/16) (by norm_num) c0357

theorem c0358 : checkPiece pa19 (2775/16) 0 (2775/16) (5625/32) = true := by decide +kernel
theorem n0358 : NonnegOnQ (2775/16) (5625/32) :=
  nonnegOn_of_checkPiece_zero (2775/16) (5625/32) (by norm_num) c0358

theorem c0359 : checkPiece pa19 (5625/32) 0 (5625/32) (1425/8) = true := by decide +kernel
theorem n0359 : NonnegOnQ (5625/32) (1425/8) :=
  nonnegOn_of_checkPiece_zero (5625/32) (1425/8) (by norm_num) c0359

theorem c0360 : checkPiece pa19 (1425/8) 0 (1425/8) (2925/16) = true := by decide +kernel
theorem n0360 : NonnegOnQ (1425/8) (2925/16) :=
  nonnegOn_of_checkPiece_zero (1425/8) (2925/16) (by norm_num) c0360

theorem c0361 : checkPiece pa19 (2925/16) 0 (2925/16) (375/2) = true := by decide +kernel
theorem n0361 : NonnegOnQ (2925/16) (375/2) :=
  nonnegOn_of_checkPiece_zero (2925/16) (375/2) (by norm_num) c0361

theorem c0362 : checkPiece pa19 (375/2) 0 (375/2) (6075/32) = true := by decide +kernel
theorem n0362 : NonnegOnQ (375/2) (6075/32) :=
  nonnegOn_of_checkPiece_zero (375/2) (6075/32) (by norm_num) c0362

theorem c0363 : checkPiece pa19 (6075/32) 0 (6075/32) (12225/64) = true := by decide +kernel
theorem n0363 : NonnegOnQ (6075/32) (12225/64) :=
  nonnegOn_of_checkPiece_zero (6075/32) (12225/64) (by norm_num) c0363

theorem c0364 : checkPiece pa19 (12225/64) 0 (12225/64) (3075/16) = true := by decide +kernel
theorem n0364 : NonnegOnQ (12225/64) (3075/16) :=
  nonnegOn_of_checkPiece_zero (12225/64) (3075/16) (by norm_num) c0364

theorem c0365 : checkPiece pa19 (3075/16) 0 (3075/16) (1575/8) = true := by decide +kernel
theorem n0365 : NonnegOnQ (3075/16) (1575/8) :=
  nonnegOn_of_checkPiece_zero (3075/16) (1575/8) (by norm_num) c0365

theorem c0366 : checkPiece pa19 (1575/8) 0 (1575/8) (825/4) = true := by decide +kernel
theorem n0366 : NonnegOnQ (1575/8) (825/4) :=
  nonnegOn_of_checkPiece_zero (1575/8) (825/4) (by norm_num) c0366

theorem c0367 : checkPiece pa19 (825/4) 0 (825/4) (1725/8) = true := by decide +kernel
theorem n0367 : NonnegOnQ (825/4) (1725/8) :=
  nonnegOn_of_checkPiece_zero (825/4) (1725/8) (by norm_num) c0367

theorem c0368 : checkPiece pa19 (1725/8) 0 (1725/8) (225) = true := by decide +kernel
theorem n0368 : NonnegOnQ (1725/8) (225) :=
  nonnegOn_of_checkPiece_zero (1725/8) (225) (by norm_num) c0368

theorem c0369 : checkPiece pa19 (225) 0 (225) (1875/8) = true := by decide +kernel
theorem n0369 : NonnegOnQ (225) (1875/8) :=
  nonnegOn_of_checkPiece_zero (225) (1875/8) (by norm_num) c0369

theorem c0370 : checkPiece pa19 (1875/8) 0 (1875/8) (975/4) = true := by decide +kernel
theorem n0370 : NonnegOnQ (1875/8) (975/4) :=
  nonnegOn_of_checkPiece_zero (1875/8) (975/4) (by norm_num) c0370

theorem c0371 : checkPiece pa19 (975/4) 0 (975/4) (2025/8) = true := by decide +kernel
theorem n0371 : NonnegOnQ (975/4) (2025/8) :=
  nonnegOn_of_checkPiece_zero (975/4) (2025/8) (by norm_num) c0371

theorem c0372 : checkPiece pa19 (2025/8) 0 (2025/8) (525/2) = true := by decide +kernel
theorem n0372 : NonnegOnQ (2025/8) (525/2) :=
  nonnegOn_of_checkPiece_zero (2025/8) (525/2) (by norm_num) c0372

theorem c0373 : checkPiece pa19 (525/2) 0 (525/2) (1125/4) = true := by decide +kernel
theorem n0373 : NonnegOnQ (525/2) (1125/4) :=
  nonnegOn_of_checkPiece_zero (525/2) (1125/4) (by norm_num) c0373

theorem c0374 : checkPiece pa19 (1125/4) 0 (1125/4) (300) = true := by decide +kernel
theorem n0374 : NonnegOnQ (1125/4) (300) :=
  nonnegOn_of_checkPiece_zero (1125/4) (300) (by norm_num) c0374

/- Original contiguous interval fold, staged to bound Lean memory use. -/
set_option maxRecDepth 4096 in
theorem foldTo0374 : NonnegOnQ 0 (300) := by
  have h330 := foldTo0330
  have h331 : NonnegOnQ 0 (3375/32) := nonnegOn_union 0 (825/8) (3375/32) h330 n0331
  have h332 : NonnegOnQ 0 (1725/16) := nonnegOn_union 0 (3375/32) (1725/16) h331 n0332
  have h333 : NonnegOnQ 0 (3525/32) := nonnegOn_union 0 (1725/16) (3525/32) h332 n0333
  have h334 : NonnegOnQ 0 (225/2) := nonnegOn_union 0 (3525/32) (225/2) h333 n0334
  have h335 : NonnegOnQ 0 (3675/32) := nonnegOn_union 0 (225/2) (3675/32) h334 n0335
  have h336 : NonnegOnQ 0 (1875/16) := nonnegOn_union 0 (3675/32) (1875/16) h335 n0336
  have h337 : NonnegOnQ 0 (3825/32) := nonnegOn_union 0 (1875/16) (3825/32) h336 n0337
  have h338 : NonnegOnQ 0 (975/8) := nonnegOn_union 0 (3825/32) (975/8) h337 n0338
  have h339 : NonnegOnQ 0 (2025/16) := nonnegOn_union 0 (975/8) (2025/16) h338 n0339
  have h340 : NonnegOnQ 0 (4125/32) := nonnegOn_union 0 (2025/16) (4125/32) h339 n0340
  have h341 : NonnegOnQ 0 (525/4) := nonnegOn_union 0 (4125/32) (525/4) h340 n0341
  have h342 : NonnegOnQ 0 (4275/32) := nonnegOn_union 0 (525/4) (4275/32) h341 n0342
  have h343 : NonnegOnQ 0 (8625/64) := nonnegOn_union 0 (4275/32) (8625/64) h342 n0343
  have h344 : NonnegOnQ 0 (2175/16) := nonnegOn_union 0 (8625/64) (2175/16) h343 n0344
  have h345 : NonnegOnQ 0 (8775/64) := nonnegOn_union 0 (2175/16) (8775/64) h344 n0345
  have h346 : NonnegOnQ 0 (4425/32) := nonnegOn_union 0 (8775/64) (4425/32) h345 n0346
  have h347 : NonnegOnQ 0 (1125/8) := nonnegOn_union 0 (4425/32) (1125/8) h346 n0347
  have h348 : NonnegOnQ 0 (2325/16) := nonnegOn_union 0 (1125/8) (2325/16) h347 n0348
  have h349 : NonnegOnQ 0 (150) := nonnegOn_union 0 (2325/16) (150) h348 n0349
  have h350 : NonnegOnQ 0 (4875/32) := nonnegOn_union 0 (150) (4875/32) h349 n0350
  have h351 : NonnegOnQ 0 (2475/16) := nonnegOn_union 0 (4875/32) (2475/16) h350 n0351
  have h352 : NonnegOnQ 0 (1275/8) := nonnegOn_union 0 (2475/16) (1275/8) h351 n0352
  have h353 : NonnegOnQ 0 (5175/32) := nonnegOn_union 0 (1275/8) (5175/32) h352 n0353
  have h354 : NonnegOnQ 0 (2625/16) := nonnegOn_union 0 (5175/32) (2625/16) h353 n0354
  have h355 : NonnegOnQ 0 (5325/32) := nonnegOn_union 0 (2625/16) (5325/32) h354 n0355
  have h356 : NonnegOnQ 0 (675/4) := nonnegOn_union 0 (5325/32) (675/4) h355 n0356
  have h357 : NonnegOnQ 0 (2775/16) := nonnegOn_union 0 (675/4) (2775/16) h356 n0357
  have h358 : NonnegOnQ 0 (5625/32) := nonnegOn_union 0 (2775/16) (5625/32) h357 n0358
  have h359 : NonnegOnQ 0 (1425/8) := nonnegOn_union 0 (5625/32) (1425/8) h358 n0359
  have h360 : NonnegOnQ 0 (2925/16) := nonnegOn_union 0 (1425/8) (2925/16) h359 n0360
  have h361 : NonnegOnQ 0 (375/2) := nonnegOn_union 0 (2925/16) (375/2) h360 n0361
  have h362 : NonnegOnQ 0 (6075/32) := nonnegOn_union 0 (375/2) (6075/32) h361 n0362
  have h363 : NonnegOnQ 0 (12225/64) := nonnegOn_union 0 (6075/32) (12225/64) h362 n0363
  have h364 : NonnegOnQ 0 (3075/16) := nonnegOn_union 0 (12225/64) (3075/16) h363 n0364
  have h365 : NonnegOnQ 0 (1575/8) := nonnegOn_union 0 (3075/16) (1575/8) h364 n0365
  have h366 : NonnegOnQ 0 (825/4) := nonnegOn_union 0 (1575/8) (825/4) h365 n0366
  have h367 : NonnegOnQ 0 (1725/8) := nonnegOn_union 0 (825/4) (1725/8) h366 n0367
  have h368 : NonnegOnQ 0 (225) := nonnegOn_union 0 (1725/8) (225) h367 n0368
  have h369 : NonnegOnQ 0 (1875/8) := nonnegOn_union 0 (225) (1875/8) h368 n0369
  have h370 : NonnegOnQ 0 (975/4) := nonnegOn_union 0 (1875/8) (975/4) h369 n0370
  have h371 : NonnegOnQ 0 (2025/8) := nonnegOn_union 0 (975/4) (2025/8) h370 n0371
  have h372 : NonnegOnQ 0 (525/2) := nonnegOn_union 0 (2025/8) (525/2) h371 n0372
  have h373 : NonnegOnQ 0 (1125/4) := nonnegOn_union 0 (525/2) (1125/4) h372 n0373
  have h374 : NonnegOnQ 0 (300) := nonnegOn_union 0 (1125/4) (300) h373 n0374
  exact h374

end AEGIS.RHKreinTrigramAdaptiveV1
