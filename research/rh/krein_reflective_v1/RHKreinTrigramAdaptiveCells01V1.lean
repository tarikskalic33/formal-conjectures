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
import RHKreinTrigramAdaptiveCoreV1

set_option autoImplicit false
noncomputable section
namespace AEGIS.RHKreinTrigramAdaptiveV1
open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinCellBatchV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinFirstCellV1
open AEGIS.RHKreinSecondCellReductionV1

theorem c0002 : checkPiece pa19 (225/8192) 0 (225/8192) (525/16384) = true := by decide +kernel
theorem n0002 : NonnegOnQ (225/8192) (525/16384) :=
  nonnegOn_of_checkPiece_zero (225/8192) (525/16384) (by norm_num) c0002

theorem c0003 : checkPiece pa19 (525/16384) 0 (525/16384) (75/2048) = true := by decide +kernel
theorem n0003 : NonnegOnQ (525/16384) (75/2048) :=
  nonnegOn_of_checkPiece_zero (525/16384) (75/2048) (by norm_num) c0003

theorem c0004 : checkPiece pa19 (75/2048) 0 (75/2048) (375/8192) = true := by decide +kernel
theorem n0004 : NonnegOnQ (75/2048) (375/8192) :=
  nonnegOn_of_checkPiece_zero (75/2048) (375/8192) (by norm_num) c0004

theorem c0005 : checkPiece pa19 (375/8192) 0 (375/8192) (225/4096) = true := by decide +kernel
theorem n0005 : NonnegOnQ (375/8192) (225/4096) :=
  nonnegOn_of_checkPiece_zero (375/8192) (225/4096) (by norm_num) c0005

theorem c0006 : checkPiece pa19 (225/4096) 0 (225/4096) (525/8192) = true := by decide +kernel
theorem n0006 : NonnegOnQ (225/4096) (525/8192) :=
  nonnegOn_of_checkPiece_zero (225/4096) (525/8192) (by norm_num) c0006

theorem c0007 : checkPiece pa19 (525/8192) 0 (525/8192) (75/1024) = true := by decide +kernel
theorem n0007 : NonnegOnQ (525/8192) (75/1024) :=
  nonnegOn_of_checkPiece_zero (525/8192) (75/1024) (by norm_num) c0007

theorem c0008 : checkPiece pa19 (75/1024) 0 (75/1024) (675/8192) = true := by decide +kernel
theorem n0008 : NonnegOnQ (75/1024) (675/8192) :=
  nonnegOn_of_checkPiece_zero (75/1024) (675/8192) (by norm_num) c0008

theorem c0009 : checkPiece pa19 (675/8192) 0 (675/8192) (375/4096) = true := by decide +kernel
theorem n0009 : NonnegOnQ (675/8192) (375/4096) :=
  nonnegOn_of_checkPiece_zero (675/8192) (375/4096) (by norm_num) c0009

theorem c0010 : checkPiece pa19 (375/4096) 0 (375/4096) (825/8192) = true := by decide +kernel
theorem n0010 : NonnegOnQ (375/4096) (825/8192) :=
  nonnegOn_of_checkPiece_zero (375/4096) (825/8192) (by norm_num) c0010

theorem c0011 : checkPiece pa19 (825/8192) 0 (825/8192) (225/2048) = true := by decide +kernel
theorem n0011 : NonnegOnQ (825/8192) (225/2048) :=
  nonnegOn_of_checkPiece_zero (825/8192) (225/2048) (by norm_num) c0011

theorem c0012 : checkPiece pa19 (225/2048) 0 (225/2048) (975/8192) = true := by decide +kernel
theorem n0012 : NonnegOnQ (225/2048) (975/8192) :=
  nonnegOn_of_checkPiece_zero (225/2048) (975/8192) (by norm_num) c0012

theorem c0013 : checkPiece pa19 (975/8192) 0 (975/8192) (525/4096) = true := by decide +kernel
theorem n0013 : NonnegOnQ (975/8192) (525/4096) :=
  nonnegOn_of_checkPiece_zero (975/8192) (525/4096) (by norm_num) c0013

theorem c0014 : checkPiece pa19 (525/4096) 0 (525/4096) (1125/8192) = true := by decide +kernel
theorem n0014 : NonnegOnQ (525/4096) (1125/8192) :=
  nonnegOn_of_checkPiece_zero (525/4096) (1125/8192) (by norm_num) c0014

theorem c0015 : checkPiece pa19 (1125/8192) 0 (1125/8192) (75/512) = true := by decide +kernel
theorem n0015 : NonnegOnQ (1125/8192) (75/512) :=
  nonnegOn_of_checkPiece_zero (1125/8192) (75/512) (by norm_num) c0015

theorem c0016 : checkPiece pa19 (75/512) 0 (75/512) (1275/8192) = true := by decide +kernel
theorem n0016 : NonnegOnQ (75/512) (1275/8192) :=
  nonnegOn_of_checkPiece_zero (75/512) (1275/8192) (by norm_num) c0016

theorem c0017 : checkPiece pa19 (1275/8192) 0 (1275/8192) (675/4096) = true := by decide +kernel
theorem n0017 : NonnegOnQ (1275/8192) (675/4096) :=
  nonnegOn_of_checkPiece_zero (1275/8192) (675/4096) (by norm_num) c0017

theorem c0018 : checkPiece pa19 (675/4096) 0 (675/4096) (1425/8192) = true := by decide +kernel
theorem n0018 : NonnegOnQ (675/4096) (1425/8192) :=
  nonnegOn_of_checkPiece_zero (675/4096) (1425/8192) (by norm_num) c0018

theorem c0019 : checkPiece pa19 (1425/8192) 0 (1425/8192) (375/2048) = true := by decide +kernel
theorem n0019 : NonnegOnQ (1425/8192) (375/2048) :=
  nonnegOn_of_checkPiece_zero (1425/8192) (375/2048) (by norm_num) c0019

theorem c0020 : checkPiece pa19 (375/2048) 0 (375/2048) (1575/8192) = true := by decide +kernel
theorem n0020 : NonnegOnQ (375/2048) (1575/8192) :=
  nonnegOn_of_checkPiece_zero (375/2048) (1575/8192) (by norm_num) c0020

theorem c0021 : checkPiece pa19 (1575/8192) 0 (1575/8192) (825/4096) = true := by decide +kernel
theorem n0021 : NonnegOnQ (1575/8192) (825/4096) :=
  nonnegOn_of_checkPiece_zero (1575/8192) (825/4096) (by norm_num) c0021

theorem c0022 : checkPiece pa19 (825/4096) 0 (825/4096) (1725/8192) = true := by decide +kernel
theorem n0022 : NonnegOnQ (825/4096) (1725/8192) :=
  nonnegOn_of_checkPiece_zero (825/4096) (1725/8192) (by norm_num) c0022

theorem c0023 : checkPiece pa19 (1725/8192) 0 (1725/8192) (225/1024) = true := by decide +kernel
theorem n0023 : NonnegOnQ (1725/8192) (225/1024) :=
  nonnegOn_of_checkPiece_zero (1725/8192) (225/1024) (by norm_num) c0023

theorem c0024 : checkPiece pa19 (225/1024) 0 (225/1024) (1875/8192) = true := by decide +kernel
theorem n0024 : NonnegOnQ (225/1024) (1875/8192) :=
  nonnegOn_of_checkPiece_zero (225/1024) (1875/8192) (by norm_num) c0024

theorem c0025 : checkPiece pa19 (1875/8192) 0 (1875/8192) (975/4096) = true := by decide +kernel
theorem n0025 : NonnegOnQ (1875/8192) (975/4096) :=
  nonnegOn_of_checkPiece_zero (1875/8192) (975/4096) (by norm_num) c0025

theorem c0026 : checkPiece pa19 (975/4096) 0 (975/4096) (2025/8192) = true := by decide +kernel
theorem n0026 : NonnegOnQ (975/4096) (2025/8192) :=
  nonnegOn_of_checkPiece_zero (975/4096) (2025/8192) (by norm_num) c0026

theorem c0027 : checkPiece pa19 (2025/8192) 0 (2025/8192) (525/2048) = true := by decide +kernel
theorem n0027 : NonnegOnQ (2025/8192) (525/2048) :=
  nonnegOn_of_checkPiece_zero (2025/8192) (525/2048) (by norm_num) c0027

theorem c0028 : checkPiece pa19 (525/2048) 0 (525/2048) (2175/8192) = true := by decide +kernel
theorem n0028 : NonnegOnQ (525/2048) (2175/8192) :=
  nonnegOn_of_checkPiece_zero (525/2048) (2175/8192) (by norm_num) c0028

theorem c0029 : checkPiece pa19 (2175/8192) 0 (2175/8192) (1125/4096) = true := by decide +kernel
theorem n0029 : NonnegOnQ (2175/8192) (1125/4096) :=
  nonnegOn_of_checkPiece_zero (2175/8192) (1125/4096) (by norm_num) c0029

theorem c0030 : checkPiece pa19 (1125/4096) 0 (1125/4096) (2325/8192) = true := by decide +kernel
theorem n0030 : NonnegOnQ (1125/4096) (2325/8192) :=
  nonnegOn_of_checkPiece_zero (1125/4096) (2325/8192) (by norm_num) c0030

theorem c0031 : checkPiece pa19 (2325/8192) 0 (2325/8192) (75/256) = true := by decide +kernel
theorem n0031 : NonnegOnQ (2325/8192) (75/256) :=
  nonnegOn_of_checkPiece_zero (2325/8192) (75/256) (by norm_num) c0031

theorem c0032 : checkPiece pa19 (75/256) 0 (75/256) (2475/8192) = true := by decide +kernel
theorem n0032 : NonnegOnQ (75/256) (2475/8192) :=
  nonnegOn_of_checkPiece_zero (75/256) (2475/8192) (by norm_num) c0032

theorem c0033 : checkPiece pa19 (2475/8192) 0 (2475/8192) (1275/4096) = true := by decide +kernel
theorem n0033 : NonnegOnQ (2475/8192) (1275/4096) :=
  nonnegOn_of_checkPiece_zero (2475/8192) (1275/4096) (by norm_num) c0033

theorem c0034 : checkPiece pa19 (1275/4096) 0 (1275/4096) (2625/8192) = true := by decide +kernel
theorem n0034 : NonnegOnQ (1275/4096) (2625/8192) :=
  nonnegOn_of_checkPiece_zero (1275/4096) (2625/8192) (by norm_num) c0034

theorem c0035 : checkPiece pa19 (2625/8192) 0 (2625/8192) (675/2048) = true := by decide +kernel
theorem n0035 : NonnegOnQ (2625/8192) (675/2048) :=
  nonnegOn_of_checkPiece_zero (2625/8192) (675/2048) (by norm_num) c0035

theorem c0036 : checkPiece pa19 (675/2048) 0 (675/2048) (2775/8192) = true := by decide +kernel
theorem n0036 : NonnegOnQ (675/2048) (2775/8192) :=
  nonnegOn_of_checkPiece_zero (675/2048) (2775/8192) (by norm_num) c0036

theorem c0037 : checkPiece pa19 (2775/8192) 0 (2775/8192) (1425/4096) = true := by decide +kernel
theorem n0037 : NonnegOnQ (2775/8192) (1425/4096) :=
  nonnegOn_of_checkPiece_zero (2775/8192) (1425/4096) (by norm_num) c0037

theorem c0038 : checkPiece pa19 (1425/4096) 0 (1425/4096) (2925/8192) = true := by decide +kernel
theorem n0038 : NonnegOnQ (1425/4096) (2925/8192) :=
  nonnegOn_of_checkPiece_zero (1425/4096) (2925/8192) (by norm_num) c0038

theorem c0039 : checkPiece pa19 (2925/8192) 0 (2925/8192) (375/1024) = true := by decide +kernel
theorem n0039 : NonnegOnQ (2925/8192) (375/1024) :=
  nonnegOn_of_checkPiece_zero (2925/8192) (375/1024) (by norm_num) c0039

theorem c0040 : checkPiece pa19 (375/1024) 0 (375/1024) (3075/8192) = true := by decide +kernel
theorem n0040 : NonnegOnQ (375/1024) (3075/8192) :=
  nonnegOn_of_checkPiece_zero (375/1024) (3075/8192) (by norm_num) c0040

theorem c0041 : checkPiece pa19 (3075/8192) 0 (3075/8192) (1575/4096) = true := by decide +kernel
theorem n0041 : NonnegOnQ (3075/8192) (1575/4096) :=
  nonnegOn_of_checkPiece_zero (3075/8192) (1575/4096) (by norm_num) c0041

theorem c0042 : checkPiece pa19 (1575/4096) 0 (1575/4096) (3225/8192) = true := by decide +kernel
theorem n0042 : NonnegOnQ (1575/4096) (3225/8192) :=
  nonnegOn_of_checkPiece_zero (1575/4096) (3225/8192) (by norm_num) c0042

theorem c0043 : checkPiece pa19 (3225/8192) 0 (3225/8192) (825/2048) = true := by decide +kernel
theorem n0043 : NonnegOnQ (3225/8192) (825/2048) :=
  nonnegOn_of_checkPiece_zero (3225/8192) (825/2048) (by norm_num) c0043

theorem c0044 : checkPiece pa19 (825/2048) 0 (825/2048) (3375/8192) = true := by decide +kernel
theorem n0044 : NonnegOnQ (825/2048) (3375/8192) :=
  nonnegOn_of_checkPiece_zero (825/2048) (3375/8192) (by norm_num) c0044

theorem c0045 : checkPiece pa19 (3375/8192) 0 (3375/8192) (1725/4096) = true := by decide +kernel
theorem n0045 : NonnegOnQ (3375/8192) (1725/4096) :=
  nonnegOn_of_checkPiece_zero (3375/8192) (1725/4096) (by norm_num) c0045

theorem c0046 : checkPiece pa19 (1725/4096) 0 (1725/4096) (3525/8192) = true := by decide +kernel
theorem n0046 : NonnegOnQ (1725/4096) (3525/8192) :=
  nonnegOn_of_checkPiece_zero (1725/4096) (3525/8192) (by norm_num) c0046

theorem c0047 : checkPiece pa19 (3525/8192) 0 (3525/8192) (225/512) = true := by decide +kernel
theorem n0047 : NonnegOnQ (3525/8192) (225/512) :=
  nonnegOn_of_checkPiece_zero (3525/8192) (225/512) (by norm_num) c0047

theorem c0048 : checkPiece pa19 (225/512) 0 (225/512) (3675/8192) = true := by decide +kernel
theorem n0048 : NonnegOnQ (225/512) (3675/8192) :=
  nonnegOn_of_checkPiece_zero (225/512) (3675/8192) (by norm_num) c0048

/- Original contiguous interval fold, staged to bound Lean memory use. -/
set_option maxRecDepth 4096 in
theorem foldTo0048 : NonnegOnQ 0 (3675/8192) := by
  have h0 := n0000
  have h1 : NonnegOnQ 0 (225/8192) := nonnegOn_union 0 (75/4096) (225/8192) h0 n0001
  have h2 : NonnegOnQ 0 (525/16384) := nonnegOn_union 0 (225/8192) (525/16384) h1 n0002
  have h3 : NonnegOnQ 0 (75/2048) := nonnegOn_union 0 (525/16384) (75/2048) h2 n0003
  have h4 : NonnegOnQ 0 (375/8192) := nonnegOn_union 0 (75/2048) (375/8192) h3 n0004
  have h5 : NonnegOnQ 0 (225/4096) := nonnegOn_union 0 (375/8192) (225/4096) h4 n0005
  have h6 : NonnegOnQ 0 (525/8192) := nonnegOn_union 0 (225/4096) (525/8192) h5 n0006
  have h7 : NonnegOnQ 0 (75/1024) := nonnegOn_union 0 (525/8192) (75/1024) h6 n0007
  have h8 : NonnegOnQ 0 (675/8192) := nonnegOn_union 0 (75/1024) (675/8192) h7 n0008
  have h9 : NonnegOnQ 0 (375/4096) := nonnegOn_union 0 (675/8192) (375/4096) h8 n0009
  have h10 : NonnegOnQ 0 (825/8192) := nonnegOn_union 0 (375/4096) (825/8192) h9 n0010
  have h11 : NonnegOnQ 0 (225/2048) := nonnegOn_union 0 (825/8192) (225/2048) h10 n0011
  have h12 : NonnegOnQ 0 (975/8192) := nonnegOn_union 0 (225/2048) (975/8192) h11 n0012
  have h13 : NonnegOnQ 0 (525/4096) := nonnegOn_union 0 (975/8192) (525/4096) h12 n0013
  have h14 : NonnegOnQ 0 (1125/8192) := nonnegOn_union 0 (525/4096) (1125/8192) h13 n0014
  have h15 : NonnegOnQ 0 (75/512) := nonnegOn_union 0 (1125/8192) (75/512) h14 n0015
  have h16 : NonnegOnQ 0 (1275/8192) := nonnegOn_union 0 (75/512) (1275/8192) h15 n0016
  have h17 : NonnegOnQ 0 (675/4096) := nonnegOn_union 0 (1275/8192) (675/4096) h16 n0017
  have h18 : NonnegOnQ 0 (1425/8192) := nonnegOn_union 0 (675/4096) (1425/8192) h17 n0018
  have h19 : NonnegOnQ 0 (375/2048) := nonnegOn_union 0 (1425/8192) (375/2048) h18 n0019
  have h20 : NonnegOnQ 0 (1575/8192) := nonnegOn_union 0 (375/2048) (1575/8192) h19 n0020
  have h21 : NonnegOnQ 0 (825/4096) := nonnegOn_union 0 (1575/8192) (825/4096) h20 n0021
  have h22 : NonnegOnQ 0 (1725/8192) := nonnegOn_union 0 (825/4096) (1725/8192) h21 n0022
  have h23 : NonnegOnQ 0 (225/1024) := nonnegOn_union 0 (1725/8192) (225/1024) h22 n0023
  have h24 : NonnegOnQ 0 (1875/8192) := nonnegOn_union 0 (225/1024) (1875/8192) h23 n0024
  have h25 : NonnegOnQ 0 (975/4096) := nonnegOn_union 0 (1875/8192) (975/4096) h24 n0025
  have h26 : NonnegOnQ 0 (2025/8192) := nonnegOn_union 0 (975/4096) (2025/8192) h25 n0026
  have h27 : NonnegOnQ 0 (525/2048) := nonnegOn_union 0 (2025/8192) (525/2048) h26 n0027
  have h28 : NonnegOnQ 0 (2175/8192) := nonnegOn_union 0 (525/2048) (2175/8192) h27 n0028
  have h29 : NonnegOnQ 0 (1125/4096) := nonnegOn_union 0 (2175/8192) (1125/4096) h28 n0029
  have h30 : NonnegOnQ 0 (2325/8192) := nonnegOn_union 0 (1125/4096) (2325/8192) h29 n0030
  have h31 : NonnegOnQ 0 (75/256) := nonnegOn_union 0 (2325/8192) (75/256) h30 n0031
  have h32 : NonnegOnQ 0 (2475/8192) := nonnegOn_union 0 (75/256) (2475/8192) h31 n0032
  have h33 : NonnegOnQ 0 (1275/4096) := nonnegOn_union 0 (2475/8192) (1275/4096) h32 n0033
  have h34 : NonnegOnQ 0 (2625/8192) := nonnegOn_union 0 (1275/4096) (2625/8192) h33 n0034
  have h35 : NonnegOnQ 0 (675/2048) := nonnegOn_union 0 (2625/8192) (675/2048) h34 n0035
  have h36 : NonnegOnQ 0 (2775/8192) := nonnegOn_union 0 (675/2048) (2775/8192) h35 n0036
  have h37 : NonnegOnQ 0 (1425/4096) := nonnegOn_union 0 (2775/8192) (1425/4096) h36 n0037
  have h38 : NonnegOnQ 0 (2925/8192) := nonnegOn_union 0 (1425/4096) (2925/8192) h37 n0038
  have h39 : NonnegOnQ 0 (375/1024) := nonnegOn_union 0 (2925/8192) (375/1024) h38 n0039
  have h40 : NonnegOnQ 0 (3075/8192) := nonnegOn_union 0 (375/1024) (3075/8192) h39 n0040
  have h41 : NonnegOnQ 0 (1575/4096) := nonnegOn_union 0 (3075/8192) (1575/4096) h40 n0041
  have h42 : NonnegOnQ 0 (3225/8192) := nonnegOn_union 0 (1575/4096) (3225/8192) h41 n0042
  have h43 : NonnegOnQ 0 (825/2048) := nonnegOn_union 0 (3225/8192) (825/2048) h42 n0043
  have h44 : NonnegOnQ 0 (3375/8192) := nonnegOn_union 0 (825/2048) (3375/8192) h43 n0044
  have h45 : NonnegOnQ 0 (1725/4096) := nonnegOn_union 0 (3375/8192) (1725/4096) h44 n0045
  have h46 : NonnegOnQ 0 (3525/8192) := nonnegOn_union 0 (1725/4096) (3525/8192) h45 n0046
  have h47 : NonnegOnQ 0 (225/512) := nonnegOn_union 0 (3525/8192) (225/512) h46 n0047
  have h48 : NonnegOnQ 0 (3675/8192) := nonnegOn_union 0 (225/512) (3675/8192) h47 n0048
  exact h48

end AEGIS.RHKreinTrigramAdaptiveV1
