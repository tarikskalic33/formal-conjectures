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
import RHKreinTrigramAdaptiveCells01V1

set_option autoImplicit false
noncomputable section
namespace AEGIS.RHKreinTrigramAdaptiveV1
open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinCellBatchV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinFirstCellV1
open AEGIS.RHKreinSecondCellReductionV1

theorem c0049 : checkPiece pa19 (3675/8192) 0 (3675/8192) (1875/4096) = true := by decide +kernel
theorem n0049 : NonnegOnQ (3675/8192) (1875/4096) :=
  nonnegOn_of_checkPiece_zero (3675/8192) (1875/4096) (by norm_num) c0049

theorem c0050 : checkPiece pa19 (1875/4096) 0 (1875/4096) (3825/8192) = true := by decide +kernel
theorem n0050 : NonnegOnQ (1875/4096) (3825/8192) :=
  nonnegOn_of_checkPiece_zero (1875/4096) (3825/8192) (by norm_num) c0050

theorem c0051 : checkPiece pa19 (3825/8192) 0 (3825/8192) (975/2048) = true := by decide +kernel
theorem n0051 : NonnegOnQ (3825/8192) (975/2048) :=
  nonnegOn_of_checkPiece_zero (3825/8192) (975/2048) (by norm_num) c0051

theorem c0052 : checkPiece pa19 (975/2048) 0 (975/2048) (3975/8192) = true := by decide +kernel
theorem n0052 : NonnegOnQ (975/2048) (3975/8192) :=
  nonnegOn_of_checkPiece_zero (975/2048) (3975/8192) (by norm_num) c0052

theorem c0053 : checkPiece pa19 (3975/8192) 0 (3975/8192) (2025/4096) = true := by decide +kernel
theorem n0053 : NonnegOnQ (3975/8192) (2025/4096) :=
  nonnegOn_of_checkPiece_zero (3975/8192) (2025/4096) (by norm_num) c0053

theorem c0054 : checkPiece pa19 (2025/4096) 0 (2025/4096) (4125/8192) = true := by decide +kernel
theorem n0054 : NonnegOnQ (2025/4096) (4125/8192) :=
  nonnegOn_of_checkPiece_zero (2025/4096) (4125/8192) (by norm_num) c0054

theorem c0055 : checkPiece pa19 (4125/8192) 0 (4125/8192) (525/1024) = true := by decide +kernel
theorem n0055 : NonnegOnQ (4125/8192) (525/1024) :=
  nonnegOn_of_checkPiece_zero (4125/8192) (525/1024) (by norm_num) c0055

theorem c0056 : checkPiece pa19 (525/1024) 0 (525/1024) (4275/8192) = true := by decide +kernel
theorem n0056 : NonnegOnQ (525/1024) (4275/8192) :=
  nonnegOn_of_checkPiece_zero (525/1024) (4275/8192) (by norm_num) c0056

theorem c0057 : checkPiece pa19 (4275/8192) 0 (4275/8192) (2175/4096) = true := by decide +kernel
theorem n0057 : NonnegOnQ (4275/8192) (2175/4096) :=
  nonnegOn_of_checkPiece_zero (4275/8192) (2175/4096) (by norm_num) c0057

theorem c0058 : checkPiece pa19 (2175/4096) 0 (2175/4096) (4425/8192) = true := by decide +kernel
theorem n0058 : NonnegOnQ (2175/4096) (4425/8192) :=
  nonnegOn_of_checkPiece_zero (2175/4096) (4425/8192) (by norm_num) c0058

theorem c0059 : checkPiece pa19 (4425/8192) 0 (4425/8192) (1125/2048) = true := by decide +kernel
theorem n0059 : NonnegOnQ (4425/8192) (1125/2048) :=
  nonnegOn_of_checkPiece_zero (4425/8192) (1125/2048) (by norm_num) c0059

theorem c0060 : checkPiece pa19 (1125/2048) 0 (1125/2048) (4575/8192) = true := by decide +kernel
theorem n0060 : NonnegOnQ (1125/2048) (4575/8192) :=
  nonnegOn_of_checkPiece_zero (1125/2048) (4575/8192) (by norm_num) c0060

theorem c0061 : checkPiece pa19 (4575/8192) 0 (4575/8192) (2325/4096) = true := by decide +kernel
theorem n0061 : NonnegOnQ (4575/8192) (2325/4096) :=
  nonnegOn_of_checkPiece_zero (4575/8192) (2325/4096) (by norm_num) c0061

theorem c0062 : checkPiece pa19 (2325/4096) 0 (2325/4096) (4725/8192) = true := by decide +kernel
theorem n0062 : NonnegOnQ (2325/4096) (4725/8192) :=
  nonnegOn_of_checkPiece_zero (2325/4096) (4725/8192) (by norm_num) c0062

theorem c0063 : checkPiece pa19 (4725/8192) 0 (4725/8192) (75/128) = true := by decide +kernel
theorem n0063 : NonnegOnQ (4725/8192) (75/128) :=
  nonnegOn_of_checkPiece_zero (4725/8192) (75/128) (by norm_num) c0063

theorem c0064 : checkPiece pa19 (75/128) 0 (75/128) (4875/8192) = true := by decide +kernel
theorem n0064 : NonnegOnQ (75/128) (4875/8192) :=
  nonnegOn_of_checkPiece_zero (75/128) (4875/8192) (by norm_num) c0064

theorem c0065 : checkPiece pa19 (4875/8192) 0 (4875/8192) (2475/4096) = true := by decide +kernel
theorem n0065 : NonnegOnQ (4875/8192) (2475/4096) :=
  nonnegOn_of_checkPiece_zero (4875/8192) (2475/4096) (by norm_num) c0065

theorem c0066 : checkPiece pa19 (2475/4096) 0 (2475/4096) (5025/8192) = true := by decide +kernel
theorem n0066 : NonnegOnQ (2475/4096) (5025/8192) :=
  nonnegOn_of_checkPiece_zero (2475/4096) (5025/8192) (by norm_num) c0066

theorem c0067 : checkPiece pa19 (5025/8192) 0 (5025/8192) (1275/2048) = true := by decide +kernel
theorem n0067 : NonnegOnQ (5025/8192) (1275/2048) :=
  nonnegOn_of_checkPiece_zero (5025/8192) (1275/2048) (by norm_num) c0067

theorem c0068 : checkPiece pa19 (1275/2048) 0 (1275/2048) (5175/8192) = true := by decide +kernel
theorem n0068 : NonnegOnQ (1275/2048) (5175/8192) :=
  nonnegOn_of_checkPiece_zero (1275/2048) (5175/8192) (by norm_num) c0068

theorem c0069 : checkPiece pa19 (5175/8192) 0 (5175/8192) (2625/4096) = true := by decide +kernel
theorem n0069 : NonnegOnQ (5175/8192) (2625/4096) :=
  nonnegOn_of_checkPiece_zero (5175/8192) (2625/4096) (by norm_num) c0069

theorem c0070 : checkPiece pa19 (2625/4096) 0 (2625/4096) (5325/8192) = true := by decide +kernel
theorem n0070 : NonnegOnQ (2625/4096) (5325/8192) :=
  nonnegOn_of_checkPiece_zero (2625/4096) (5325/8192) (by norm_num) c0070

theorem c0071 : checkPiece pa19 (5325/8192) 0 (5325/8192) (675/1024) = true := by decide +kernel
theorem n0071 : NonnegOnQ (5325/8192) (675/1024) :=
  nonnegOn_of_checkPiece_zero (5325/8192) (675/1024) (by norm_num) c0071

theorem c0072 : checkPiece pa19 (675/1024) 0 (675/1024) (5475/8192) = true := by decide +kernel
theorem n0072 : NonnegOnQ (675/1024) (5475/8192) :=
  nonnegOn_of_checkPiece_zero (675/1024) (5475/8192) (by norm_num) c0072

theorem c0073 : checkPiece pa19 (5475/8192) 0 (5475/8192) (2775/4096) = true := by decide +kernel
theorem n0073 : NonnegOnQ (5475/8192) (2775/4096) :=
  nonnegOn_of_checkPiece_zero (5475/8192) (2775/4096) (by norm_num) c0073

theorem c0074 : checkPiece pa19 (2775/4096) 0 (2775/4096) (5625/8192) = true := by decide +kernel
theorem n0074 : NonnegOnQ (2775/4096) (5625/8192) :=
  nonnegOn_of_checkPiece_zero (2775/4096) (5625/8192) (by norm_num) c0074

theorem c0075 : checkPiece pa19 (5625/8192) 0 (5625/8192) (1425/2048) = true := by decide +kernel
theorem n0075 : NonnegOnQ (5625/8192) (1425/2048) :=
  nonnegOn_of_checkPiece_zero (5625/8192) (1425/2048) (by norm_num) c0075

theorem c0076 : checkPiece pa19 (1425/2048) 0 (1425/2048) (5775/8192) = true := by decide +kernel
theorem n0076 : NonnegOnQ (1425/2048) (5775/8192) :=
  nonnegOn_of_checkPiece_zero (1425/2048) (5775/8192) (by norm_num) c0076

theorem c0077 : checkPiece pa19 (5775/8192) 0 (5775/8192) (2925/4096) = true := by decide +kernel
theorem n0077 : NonnegOnQ (5775/8192) (2925/4096) :=
  nonnegOn_of_checkPiece_zero (5775/8192) (2925/4096) (by norm_num) c0077

theorem c0078 : checkPiece pa19 (2925/4096) 0 (2925/4096) (5925/8192) = true := by decide +kernel
theorem n0078 : NonnegOnQ (2925/4096) (5925/8192) :=
  nonnegOn_of_checkPiece_zero (2925/4096) (5925/8192) (by norm_num) c0078

theorem c0079 : checkPiece pa19 (5925/8192) 0 (5925/8192) (375/512) = true := by decide +kernel
theorem n0079 : NonnegOnQ (5925/8192) (375/512) :=
  nonnegOn_of_checkPiece_zero (5925/8192) (375/512) (by norm_num) c0079

theorem c0080 : checkPiece pa19 (375/512) 0 (375/512) (6075/8192) = true := by decide +kernel
theorem n0080 : NonnegOnQ (375/512) (6075/8192) :=
  nonnegOn_of_checkPiece_zero (375/512) (6075/8192) (by norm_num) c0080

theorem c0081 : checkPiece pa19 (6075/8192) 0 (6075/8192) (3075/4096) = true := by decide +kernel
theorem n0081 : NonnegOnQ (6075/8192) (3075/4096) :=
  nonnegOn_of_checkPiece_zero (6075/8192) (3075/4096) (by norm_num) c0081

theorem c0082 : checkPiece pa19 (3075/4096) 0 (3075/4096) (6225/8192) = true := by decide +kernel
theorem n0082 : NonnegOnQ (3075/4096) (6225/8192) :=
  nonnegOn_of_checkPiece_zero (3075/4096) (6225/8192) (by norm_num) c0082

theorem c0083 : checkPiece pa19 (6225/8192) 0 (6225/8192) (1575/2048) = true := by decide +kernel
theorem n0083 : NonnegOnQ (6225/8192) (1575/2048) :=
  nonnegOn_of_checkPiece_zero (6225/8192) (1575/2048) (by norm_num) c0083

theorem c0084 : checkPiece pa19 (1575/2048) 0 (1575/2048) (6375/8192) = true := by decide +kernel
theorem n0084 : NonnegOnQ (1575/2048) (6375/8192) :=
  nonnegOn_of_checkPiece_zero (1575/2048) (6375/8192) (by norm_num) c0084

theorem c0085 : checkPiece pa19 (6375/8192) 0 (6375/8192) (3225/4096) = true := by decide +kernel
theorem n0085 : NonnegOnQ (6375/8192) (3225/4096) :=
  nonnegOn_of_checkPiece_zero (6375/8192) (3225/4096) (by norm_num) c0085

theorem c0086 : checkPiece pa19 (3225/4096) 0 (3225/4096) (6525/8192) = true := by decide +kernel
theorem n0086 : NonnegOnQ (3225/4096) (6525/8192) :=
  nonnegOn_of_checkPiece_zero (3225/4096) (6525/8192) (by norm_num) c0086

theorem c0087 : checkPiece pa19 (6525/8192) 0 (6525/8192) (825/1024) = true := by decide +kernel
theorem n0087 : NonnegOnQ (6525/8192) (825/1024) :=
  nonnegOn_of_checkPiece_zero (6525/8192) (825/1024) (by norm_num) c0087

theorem c0088 : checkPiece pa19 (825/1024) 0 (825/1024) (6675/8192) = true := by decide +kernel
theorem n0088 : NonnegOnQ (825/1024) (6675/8192) :=
  nonnegOn_of_checkPiece_zero (825/1024) (6675/8192) (by norm_num) c0088

theorem c0089 : checkPiece pa19 (6675/8192) 0 (6675/8192) (3375/4096) = true := by decide +kernel
theorem n0089 : NonnegOnQ (6675/8192) (3375/4096) :=
  nonnegOn_of_checkPiece_zero (6675/8192) (3375/4096) (by norm_num) c0089

theorem c0090 : checkPiece pa19 (3375/4096) 0 (3375/4096) (6825/8192) = true := by decide +kernel
theorem n0090 : NonnegOnQ (3375/4096) (6825/8192) :=
  nonnegOn_of_checkPiece_zero (3375/4096) (6825/8192) (by norm_num) c0090

theorem c0091 : checkPiece pa19 (6825/8192) 0 (6825/8192) (1725/2048) = true := by decide +kernel
theorem n0091 : NonnegOnQ (6825/8192) (1725/2048) :=
  nonnegOn_of_checkPiece_zero (6825/8192) (1725/2048) (by norm_num) c0091

theorem c0092 : checkPiece pa19 (1725/2048) 0 (1725/2048) (6975/8192) = true := by decide +kernel
theorem n0092 : NonnegOnQ (1725/2048) (6975/8192) :=
  nonnegOn_of_checkPiece_zero (1725/2048) (6975/8192) (by norm_num) c0092

theorem c0093 : checkPiece pa19 (6975/8192) 0 (6975/8192) (3525/4096) = true := by decide +kernel
theorem n0093 : NonnegOnQ (6975/8192) (3525/4096) :=
  nonnegOn_of_checkPiece_zero (6975/8192) (3525/4096) (by norm_num) c0093

theorem c0094 : checkPiece pa19 (3525/4096) 0 (3525/4096) (7125/8192) = true := by decide +kernel
theorem n0094 : NonnegOnQ (3525/4096) (7125/8192) :=
  nonnegOn_of_checkPiece_zero (3525/4096) (7125/8192) (by norm_num) c0094

theorem c0095 : checkPiece pa19 (7125/8192) 0 (7125/8192) (225/256) = true := by decide +kernel
theorem n0095 : NonnegOnQ (7125/8192) (225/256) :=
  nonnegOn_of_checkPiece_zero (7125/8192) (225/256) (by norm_num) c0095

/- Original contiguous interval fold, staged to bound Lean memory use. -/
set_option maxRecDepth 4096 in
theorem foldTo0095 : NonnegOnQ 0 (225/256) := by
  have h48 := foldTo0048
  have h49 : NonnegOnQ 0 (1875/4096) := nonnegOn_union 0 (3675/8192) (1875/4096) h48 n0049
  have h50 : NonnegOnQ 0 (3825/8192) := nonnegOn_union 0 (1875/4096) (3825/8192) h49 n0050
  have h51 : NonnegOnQ 0 (975/2048) := nonnegOn_union 0 (3825/8192) (975/2048) h50 n0051
  have h52 : NonnegOnQ 0 (3975/8192) := nonnegOn_union 0 (975/2048) (3975/8192) h51 n0052
  have h53 : NonnegOnQ 0 (2025/4096) := nonnegOn_union 0 (3975/8192) (2025/4096) h52 n0053
  have h54 : NonnegOnQ 0 (4125/8192) := nonnegOn_union 0 (2025/4096) (4125/8192) h53 n0054
  have h55 : NonnegOnQ 0 (525/1024) := nonnegOn_union 0 (4125/8192) (525/1024) h54 n0055
  have h56 : NonnegOnQ 0 (4275/8192) := nonnegOn_union 0 (525/1024) (4275/8192) h55 n0056
  have h57 : NonnegOnQ 0 (2175/4096) := nonnegOn_union 0 (4275/8192) (2175/4096) h56 n0057
  have h58 : NonnegOnQ 0 (4425/8192) := nonnegOn_union 0 (2175/4096) (4425/8192) h57 n0058
  have h59 : NonnegOnQ 0 (1125/2048) := nonnegOn_union 0 (4425/8192) (1125/2048) h58 n0059
  have h60 : NonnegOnQ 0 (4575/8192) := nonnegOn_union 0 (1125/2048) (4575/8192) h59 n0060
  have h61 : NonnegOnQ 0 (2325/4096) := nonnegOn_union 0 (4575/8192) (2325/4096) h60 n0061
  have h62 : NonnegOnQ 0 (4725/8192) := nonnegOn_union 0 (2325/4096) (4725/8192) h61 n0062
  have h63 : NonnegOnQ 0 (75/128) := nonnegOn_union 0 (4725/8192) (75/128) h62 n0063
  have h64 : NonnegOnQ 0 (4875/8192) := nonnegOn_union 0 (75/128) (4875/8192) h63 n0064
  have h65 : NonnegOnQ 0 (2475/4096) := nonnegOn_union 0 (4875/8192) (2475/4096) h64 n0065
  have h66 : NonnegOnQ 0 (5025/8192) := nonnegOn_union 0 (2475/4096) (5025/8192) h65 n0066
  have h67 : NonnegOnQ 0 (1275/2048) := nonnegOn_union 0 (5025/8192) (1275/2048) h66 n0067
  have h68 : NonnegOnQ 0 (5175/8192) := nonnegOn_union 0 (1275/2048) (5175/8192) h67 n0068
  have h69 : NonnegOnQ 0 (2625/4096) := nonnegOn_union 0 (5175/8192) (2625/4096) h68 n0069
  have h70 : NonnegOnQ 0 (5325/8192) := nonnegOn_union 0 (2625/4096) (5325/8192) h69 n0070
  have h71 : NonnegOnQ 0 (675/1024) := nonnegOn_union 0 (5325/8192) (675/1024) h70 n0071
  have h72 : NonnegOnQ 0 (5475/8192) := nonnegOn_union 0 (675/1024) (5475/8192) h71 n0072
  have h73 : NonnegOnQ 0 (2775/4096) := nonnegOn_union 0 (5475/8192) (2775/4096) h72 n0073
  have h74 : NonnegOnQ 0 (5625/8192) := nonnegOn_union 0 (2775/4096) (5625/8192) h73 n0074
  have h75 : NonnegOnQ 0 (1425/2048) := nonnegOn_union 0 (5625/8192) (1425/2048) h74 n0075
  have h76 : NonnegOnQ 0 (5775/8192) := nonnegOn_union 0 (1425/2048) (5775/8192) h75 n0076
  have h77 : NonnegOnQ 0 (2925/4096) := nonnegOn_union 0 (5775/8192) (2925/4096) h76 n0077
  have h78 : NonnegOnQ 0 (5925/8192) := nonnegOn_union 0 (2925/4096) (5925/8192) h77 n0078
  have h79 : NonnegOnQ 0 (375/512) := nonnegOn_union 0 (5925/8192) (375/512) h78 n0079
  have h80 : NonnegOnQ 0 (6075/8192) := nonnegOn_union 0 (375/512) (6075/8192) h79 n0080
  have h81 : NonnegOnQ 0 (3075/4096) := nonnegOn_union 0 (6075/8192) (3075/4096) h80 n0081
  have h82 : NonnegOnQ 0 (6225/8192) := nonnegOn_union 0 (3075/4096) (6225/8192) h81 n0082
  have h83 : NonnegOnQ 0 (1575/2048) := nonnegOn_union 0 (6225/8192) (1575/2048) h82 n0083
  have h84 : NonnegOnQ 0 (6375/8192) := nonnegOn_union 0 (1575/2048) (6375/8192) h83 n0084
  have h85 : NonnegOnQ 0 (3225/4096) := nonnegOn_union 0 (6375/8192) (3225/4096) h84 n0085
  have h86 : NonnegOnQ 0 (6525/8192) := nonnegOn_union 0 (3225/4096) (6525/8192) h85 n0086
  have h87 : NonnegOnQ 0 (825/1024) := nonnegOn_union 0 (6525/8192) (825/1024) h86 n0087
  have h88 : NonnegOnQ 0 (6675/8192) := nonnegOn_union 0 (825/1024) (6675/8192) h87 n0088
  have h89 : NonnegOnQ 0 (3375/4096) := nonnegOn_union 0 (6675/8192) (3375/4096) h88 n0089
  have h90 : NonnegOnQ 0 (6825/8192) := nonnegOn_union 0 (3375/4096) (6825/8192) h89 n0090
  have h91 : NonnegOnQ 0 (1725/2048) := nonnegOn_union 0 (6825/8192) (1725/2048) h90 n0091
  have h92 : NonnegOnQ 0 (6975/8192) := nonnegOn_union 0 (1725/2048) (6975/8192) h91 n0092
  have h93 : NonnegOnQ 0 (3525/4096) := nonnegOn_union 0 (6975/8192) (3525/4096) h92 n0093
  have h94 : NonnegOnQ 0 (7125/8192) := nonnegOn_union 0 (3525/4096) (7125/8192) h93 n0094
  have h95 : NonnegOnQ 0 (225/256) := nonnegOn_union 0 (7125/8192) (225/256) h94 n0095
  exact h95

end AEGIS.RHKreinTrigramAdaptiveV1
