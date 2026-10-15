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
import RHKreinTrigramAdaptiveCells02V1

set_option autoImplicit false
noncomputable section
namespace AEGIS.RHKreinTrigramAdaptiveV1
open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinCellBatchV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinFirstCellV1
open AEGIS.RHKreinSecondCellReductionV1

theorem c0096 : checkPiece pa19 (225/256) 0 (225/256) (7275/8192) = true := by decide +kernel
theorem n0096 : NonnegOnQ (225/256) (7275/8192) :=
  nonnegOn_of_checkPiece_zero (225/256) (7275/8192) (by norm_num) c0096

theorem c0097 : checkPiece pa19 (7275/8192) 0 (7275/8192) (3675/4096) = true := by decide +kernel
theorem n0097 : NonnegOnQ (7275/8192) (3675/4096) :=
  nonnegOn_of_checkPiece_zero (7275/8192) (3675/4096) (by norm_num) c0097

theorem c0098 : checkPiece pa19 (3675/4096) 0 (3675/4096) (7425/8192) = true := by decide +kernel
theorem n0098 : NonnegOnQ (3675/4096) (7425/8192) :=
  nonnegOn_of_checkPiece_zero (3675/4096) (7425/8192) (by norm_num) c0098

theorem c0099 : checkPiece pa19 (7425/8192) 0 (7425/8192) (1875/2048) = true := by decide +kernel
theorem n0099 : NonnegOnQ (7425/8192) (1875/2048) :=
  nonnegOn_of_checkPiece_zero (7425/8192) (1875/2048) (by norm_num) c0099

theorem c0100 : checkPiece pa19 (1875/2048) 0 (1875/2048) (7575/8192) = true := by decide +kernel
theorem n0100 : NonnegOnQ (1875/2048) (7575/8192) :=
  nonnegOn_of_checkPiece_zero (1875/2048) (7575/8192) (by norm_num) c0100

theorem c0101 : checkPiece pa19 (7575/8192) 0 (7575/8192) (3825/4096) = true := by decide +kernel
theorem n0101 : NonnegOnQ (7575/8192) (3825/4096) :=
  nonnegOn_of_checkPiece_zero (7575/8192) (3825/4096) (by norm_num) c0101

theorem c0102 : checkPiece pa19 (3825/4096) 0 (3825/4096) (975/1024) = true := by decide +kernel
theorem n0102 : NonnegOnQ (3825/4096) (975/1024) :=
  nonnegOn_of_checkPiece_zero (3825/4096) (975/1024) (by norm_num) c0102

theorem c0103 : checkPiece pa19 (975/1024) 0 (975/1024) (3975/4096) = true := by decide +kernel
theorem n0103 : NonnegOnQ (975/1024) (3975/4096) :=
  nonnegOn_of_checkPiece_zero (975/1024) (3975/4096) (by norm_num) c0103

theorem c0104 : checkPiece pa19 (3975/4096) 0 (3975/4096) (2025/2048) = true := by decide +kernel
theorem n0104 : NonnegOnQ (3975/4096) (2025/2048) :=
  nonnegOn_of_checkPiece_zero (3975/4096) (2025/2048) (by norm_num) c0104

theorem c0105 : checkPiece pa19 (2025/2048) 0 (2025/2048) (4125/4096) = true := by decide +kernel
theorem n0105 : NonnegOnQ (2025/2048) (4125/4096) :=
  nonnegOn_of_checkPiece_zero (2025/2048) (4125/4096) (by norm_num) c0105

theorem c0106 : checkPiece pa19 (4125/4096) 0 (4125/4096) (525/512) = true := by decide +kernel
theorem n0106 : NonnegOnQ (4125/4096) (525/512) :=
  nonnegOn_of_checkPiece_zero (4125/4096) (525/512) (by norm_num) c0106

theorem c0107 : checkPiece pa19 (525/512) 0 (525/512) (4275/4096) = true := by decide +kernel
theorem n0107 : NonnegOnQ (525/512) (4275/4096) :=
  nonnegOn_of_checkPiece_zero (525/512) (4275/4096) (by norm_num) c0107

theorem c0108 : checkPiece pa19 (4275/4096) 0 (4275/4096) (2175/2048) = true := by decide +kernel
theorem n0108 : NonnegOnQ (4275/4096) (2175/2048) :=
  nonnegOn_of_checkPiece_zero (4275/4096) (2175/2048) (by norm_num) c0108

theorem c0109 : checkPiece pa19 (2175/2048) 0 (2175/2048) (4425/4096) = true := by decide +kernel
theorem n0109 : NonnegOnQ (2175/2048) (4425/4096) :=
  nonnegOn_of_checkPiece_zero (2175/2048) (4425/4096) (by norm_num) c0109

theorem c0110 : checkPiece pa19 (4425/4096) 0 (4425/4096) (1125/1024) = true := by decide +kernel
theorem n0110 : NonnegOnQ (4425/4096) (1125/1024) :=
  nonnegOn_of_checkPiece_zero (4425/4096) (1125/1024) (by norm_num) c0110

theorem c0111 : checkPiece pa19 (1125/1024) 0 (1125/1024) (4575/4096) = true := by decide +kernel
theorem n0111 : NonnegOnQ (1125/1024) (4575/4096) :=
  nonnegOn_of_checkPiece_zero (1125/1024) (4575/4096) (by norm_num) c0111

theorem c0112 : checkPiece pa19 (4575/4096) 0 (4575/4096) (2325/2048) = true := by decide +kernel
theorem n0112 : NonnegOnQ (4575/4096) (2325/2048) :=
  nonnegOn_of_checkPiece_zero (4575/4096) (2325/2048) (by norm_num) c0112

theorem c0113 : checkPiece pa19 (2325/2048) 0 (2325/2048) (4725/4096) = true := by decide +kernel
theorem n0113 : NonnegOnQ (2325/2048) (4725/4096) :=
  nonnegOn_of_checkPiece_zero (2325/2048) (4725/4096) (by norm_num) c0113

theorem c0114 : checkPiece pa19 (4725/4096) 0 (4725/4096) (75/64) = true := by decide +kernel
theorem n0114 : NonnegOnQ (4725/4096) (75/64) :=
  nonnegOn_of_checkPiece_zero (4725/4096) (75/64) (by norm_num) c0114

theorem c0115 : checkPiece pa19 (75/64) 0 (75/64) (4875/4096) = true := by decide +kernel
theorem n0115 : NonnegOnQ (75/64) (4875/4096) :=
  nonnegOn_of_checkPiece_zero (75/64) (4875/4096) (by norm_num) c0115

theorem c0116 : checkPiece pa19 (4875/4096) 0 (4875/4096) (2475/2048) = true := by decide +kernel
theorem n0116 : NonnegOnQ (4875/4096) (2475/2048) :=
  nonnegOn_of_checkPiece_zero (4875/4096) (2475/2048) (by norm_num) c0116

theorem c0117 : checkPiece pa19 (2475/2048) 0 (2475/2048) (5025/4096) = true := by decide +kernel
theorem n0117 : NonnegOnQ (2475/2048) (5025/4096) :=
  nonnegOn_of_checkPiece_zero (2475/2048) (5025/4096) (by norm_num) c0117

theorem c0118 : checkPiece pa19 (5025/4096) 0 (5025/4096) (1275/1024) = true := by decide +kernel
theorem n0118 : NonnegOnQ (5025/4096) (1275/1024) :=
  nonnegOn_of_checkPiece_zero (5025/4096) (1275/1024) (by norm_num) c0118

theorem c0119 : checkPiece pa19 (1275/1024) 0 (1275/1024) (5175/4096) = true := by decide +kernel
theorem n0119 : NonnegOnQ (1275/1024) (5175/4096) :=
  nonnegOn_of_checkPiece_zero (1275/1024) (5175/4096) (by norm_num) c0119

theorem c0120 : checkPiece pa19 (5175/4096) 0 (5175/4096) (2625/2048) = true := by decide +kernel
theorem n0120 : NonnegOnQ (5175/4096) (2625/2048) :=
  nonnegOn_of_checkPiece_zero (5175/4096) (2625/2048) (by norm_num) c0120

theorem c0121 : checkPiece pa19 (2625/2048) 0 (2625/2048) (5325/4096) = true := by decide +kernel
theorem n0121 : NonnegOnQ (2625/2048) (5325/4096) :=
  nonnegOn_of_checkPiece_zero (2625/2048) (5325/4096) (by norm_num) c0121

theorem c0122 : checkPiece pa19 (5325/4096) 0 (5325/4096) (675/512) = true := by decide +kernel
theorem n0122 : NonnegOnQ (5325/4096) (675/512) :=
  nonnegOn_of_checkPiece_zero (5325/4096) (675/512) (by norm_num) c0122

theorem c0123 : checkPiece pa19 (675/512) 0 (675/512) (5475/4096) = true := by decide +kernel
theorem n0123 : NonnegOnQ (675/512) (5475/4096) :=
  nonnegOn_of_checkPiece_zero (675/512) (5475/4096) (by norm_num) c0123

theorem c0124 : checkPiece pa19 (5475/4096) 0 (5475/4096) (2775/2048) = true := by decide +kernel
theorem n0124 : NonnegOnQ (5475/4096) (2775/2048) :=
  nonnegOn_of_checkPiece_zero (5475/4096) (2775/2048) (by norm_num) c0124

theorem c0125 : checkPiece pa19 (2775/2048) 0 (2775/2048) (5625/4096) = true := by decide +kernel
theorem n0125 : NonnegOnQ (2775/2048) (5625/4096) :=
  nonnegOn_of_checkPiece_zero (2775/2048) (5625/4096) (by norm_num) c0125

theorem c0126 : checkPiece pa19 (5625/4096) 0 (5625/4096) (1425/1024) = true := by decide +kernel
theorem n0126 : NonnegOnQ (5625/4096) (1425/1024) :=
  nonnegOn_of_checkPiece_zero (5625/4096) (1425/1024) (by norm_num) c0126

theorem c0127 : checkPiece pa19 (1425/1024) 0 (1425/1024) (2925/2048) = true := by decide +kernel
theorem n0127 : NonnegOnQ (1425/1024) (2925/2048) :=
  nonnegOn_of_checkPiece_zero (1425/1024) (2925/2048) (by norm_num) c0127

theorem c0128 : checkPiece pa19 (2925/2048) 0 (2925/2048) (375/256) = true := by decide +kernel
theorem n0128 : NonnegOnQ (2925/2048) (375/256) :=
  nonnegOn_of_checkPiece_zero (2925/2048) (375/256) (by norm_num) c0128

theorem c0129 : checkPiece pa19 (375/256) 0 (375/256) (3075/2048) = true := by decide +kernel
theorem n0129 : NonnegOnQ (375/256) (3075/2048) :=
  nonnegOn_of_checkPiece_zero (375/256) (3075/2048) (by norm_num) c0129

theorem c0130 : checkPiece pa19 (3075/2048) 0 (3075/2048) (1575/1024) = true := by decide +kernel
theorem n0130 : NonnegOnQ (3075/2048) (1575/1024) :=
  nonnegOn_of_checkPiece_zero (3075/2048) (1575/1024) (by norm_num) c0130

theorem c0131 : checkPiece pa19 (1575/1024) 0 (1575/1024) (3225/2048) = true := by decide +kernel
theorem n0131 : NonnegOnQ (1575/1024) (3225/2048) :=
  nonnegOn_of_checkPiece_zero (1575/1024) (3225/2048) (by norm_num) c0131

theorem c0132 : checkPiece pa19 (3225/2048) 0 (3225/2048) (825/512) = true := by decide +kernel
theorem n0132 : NonnegOnQ (3225/2048) (825/512) :=
  nonnegOn_of_checkPiece_zero (3225/2048) (825/512) (by norm_num) c0132

theorem c0133 : checkPiece pa19 (825/512) 0 (825/512) (3375/2048) = true := by decide +kernel
theorem n0133 : NonnegOnQ (825/512) (3375/2048) :=
  nonnegOn_of_checkPiece_zero (825/512) (3375/2048) (by norm_num) c0133

theorem c0134 : checkPiece pa19 (3375/2048) 0 (3375/2048) (1725/1024) = true := by decide +kernel
theorem n0134 : NonnegOnQ (3375/2048) (1725/1024) :=
  nonnegOn_of_checkPiece_zero (3375/2048) (1725/1024) (by norm_num) c0134

theorem c0135 : checkPiece pa19 (1725/1024) 0 (1725/1024) (3525/2048) = true := by decide +kernel
theorem n0135 : NonnegOnQ (1725/1024) (3525/2048) :=
  nonnegOn_of_checkPiece_zero (1725/1024) (3525/2048) (by norm_num) c0135

theorem c0136 : checkPiece pa19 (3525/2048) 0 (3525/2048) (225/128) = true := by decide +kernel
theorem n0136 : NonnegOnQ (3525/2048) (225/128) :=
  nonnegOn_of_checkPiece_zero (3525/2048) (225/128) (by norm_num) c0136

theorem c0137 : checkPiece pa19 (225/128) 0 (225/128) (3675/2048) = true := by decide +kernel
theorem n0137 : NonnegOnQ (225/128) (3675/2048) :=
  nonnegOn_of_checkPiece_zero (225/128) (3675/2048) (by norm_num) c0137

theorem c0138 : checkPiece pa19 (3675/2048) 0 (3675/2048) (1875/1024) = true := by decide +kernel
theorem n0138 : NonnegOnQ (3675/2048) (1875/1024) :=
  nonnegOn_of_checkPiece_zero (3675/2048) (1875/1024) (by norm_num) c0138

theorem c0139 : checkPiece pa19 (1875/1024) 0 (1875/1024) (3825/2048) = true := by decide +kernel
theorem n0139 : NonnegOnQ (1875/1024) (3825/2048) :=
  nonnegOn_of_checkPiece_zero (1875/1024) (3825/2048) (by norm_num) c0139

theorem c0140 : checkPiece pa19 (3825/2048) 0 (3825/2048) (975/512) = true := by decide +kernel
theorem n0140 : NonnegOnQ (3825/2048) (975/512) :=
  nonnegOn_of_checkPiece_zero (3825/2048) (975/512) (by norm_num) c0140

theorem c0141 : checkPiece pa19 (975/512) 0 (975/512) (3975/2048) = true := by decide +kernel
theorem n0141 : NonnegOnQ (975/512) (3975/2048) :=
  nonnegOn_of_checkPiece_zero (975/512) (3975/2048) (by norm_num) c0141

theorem c0142 : checkPiece pa19 (3975/2048) 0 (3975/2048) (2025/1024) = true := by decide +kernel
theorem n0142 : NonnegOnQ (3975/2048) (2025/1024) :=
  nonnegOn_of_checkPiece_zero (3975/2048) (2025/1024) (by norm_num) c0142

/- Original contiguous interval fold, staged to bound Lean memory use. -/
set_option maxRecDepth 4096 in
theorem foldTo0142 : NonnegOnQ 0 (2025/1024) := by
  have h95 := foldTo0095
  have h96 : NonnegOnQ 0 (7275/8192) := nonnegOn_union 0 (225/256) (7275/8192) h95 n0096
  have h97 : NonnegOnQ 0 (3675/4096) := nonnegOn_union 0 (7275/8192) (3675/4096) h96 n0097
  have h98 : NonnegOnQ 0 (7425/8192) := nonnegOn_union 0 (3675/4096) (7425/8192) h97 n0098
  have h99 : NonnegOnQ 0 (1875/2048) := nonnegOn_union 0 (7425/8192) (1875/2048) h98 n0099
  have h100 : NonnegOnQ 0 (7575/8192) := nonnegOn_union 0 (1875/2048) (7575/8192) h99 n0100
  have h101 : NonnegOnQ 0 (3825/4096) := nonnegOn_union 0 (7575/8192) (3825/4096) h100 n0101
  have h102 : NonnegOnQ 0 (975/1024) := nonnegOn_union 0 (3825/4096) (975/1024) h101 n0102
  have h103 : NonnegOnQ 0 (3975/4096) := nonnegOn_union 0 (975/1024) (3975/4096) h102 n0103
  have h104 : NonnegOnQ 0 (2025/2048) := nonnegOn_union 0 (3975/4096) (2025/2048) h103 n0104
  have h105 : NonnegOnQ 0 (4125/4096) := nonnegOn_union 0 (2025/2048) (4125/4096) h104 n0105
  have h106 : NonnegOnQ 0 (525/512) := nonnegOn_union 0 (4125/4096) (525/512) h105 n0106
  have h107 : NonnegOnQ 0 (4275/4096) := nonnegOn_union 0 (525/512) (4275/4096) h106 n0107
  have h108 : NonnegOnQ 0 (2175/2048) := nonnegOn_union 0 (4275/4096) (2175/2048) h107 n0108
  have h109 : NonnegOnQ 0 (4425/4096) := nonnegOn_union 0 (2175/2048) (4425/4096) h108 n0109
  have h110 : NonnegOnQ 0 (1125/1024) := nonnegOn_union 0 (4425/4096) (1125/1024) h109 n0110
  have h111 : NonnegOnQ 0 (4575/4096) := nonnegOn_union 0 (1125/1024) (4575/4096) h110 n0111
  have h112 : NonnegOnQ 0 (2325/2048) := nonnegOn_union 0 (4575/4096) (2325/2048) h111 n0112
  have h113 : NonnegOnQ 0 (4725/4096) := nonnegOn_union 0 (2325/2048) (4725/4096) h112 n0113
  have h114 : NonnegOnQ 0 (75/64) := nonnegOn_union 0 (4725/4096) (75/64) h113 n0114
  have h115 : NonnegOnQ 0 (4875/4096) := nonnegOn_union 0 (75/64) (4875/4096) h114 n0115
  have h116 : NonnegOnQ 0 (2475/2048) := nonnegOn_union 0 (4875/4096) (2475/2048) h115 n0116
  have h117 : NonnegOnQ 0 (5025/4096) := nonnegOn_union 0 (2475/2048) (5025/4096) h116 n0117
  have h118 : NonnegOnQ 0 (1275/1024) := nonnegOn_union 0 (5025/4096) (1275/1024) h117 n0118
  have h119 : NonnegOnQ 0 (5175/4096) := nonnegOn_union 0 (1275/1024) (5175/4096) h118 n0119
  have h120 : NonnegOnQ 0 (2625/2048) := nonnegOn_union 0 (5175/4096) (2625/2048) h119 n0120
  have h121 : NonnegOnQ 0 (5325/4096) := nonnegOn_union 0 (2625/2048) (5325/4096) h120 n0121
  have h122 : NonnegOnQ 0 (675/512) := nonnegOn_union 0 (5325/4096) (675/512) h121 n0122
  have h123 : NonnegOnQ 0 (5475/4096) := nonnegOn_union 0 (675/512) (5475/4096) h122 n0123
  have h124 : NonnegOnQ 0 (2775/2048) := nonnegOn_union 0 (5475/4096) (2775/2048) h123 n0124
  have h125 : NonnegOnQ 0 (5625/4096) := nonnegOn_union 0 (2775/2048) (5625/4096) h124 n0125
  have h126 : NonnegOnQ 0 (1425/1024) := nonnegOn_union 0 (5625/4096) (1425/1024) h125 n0126
  have h127 : NonnegOnQ 0 (2925/2048) := nonnegOn_union 0 (1425/1024) (2925/2048) h126 n0127
  have h128 : NonnegOnQ 0 (375/256) := nonnegOn_union 0 (2925/2048) (375/256) h127 n0128
  have h129 : NonnegOnQ 0 (3075/2048) := nonnegOn_union 0 (375/256) (3075/2048) h128 n0129
  have h130 : NonnegOnQ 0 (1575/1024) := nonnegOn_union 0 (3075/2048) (1575/1024) h129 n0130
  have h131 : NonnegOnQ 0 (3225/2048) := nonnegOn_union 0 (1575/1024) (3225/2048) h130 n0131
  have h132 : NonnegOnQ 0 (825/512) := nonnegOn_union 0 (3225/2048) (825/512) h131 n0132
  have h133 : NonnegOnQ 0 (3375/2048) := nonnegOn_union 0 (825/512) (3375/2048) h132 n0133
  have h134 : NonnegOnQ 0 (1725/1024) := nonnegOn_union 0 (3375/2048) (1725/1024) h133 n0134
  have h135 : NonnegOnQ 0 (3525/2048) := nonnegOn_union 0 (1725/1024) (3525/2048) h134 n0135
  have h136 : NonnegOnQ 0 (225/128) := nonnegOn_union 0 (3525/2048) (225/128) h135 n0136
  have h137 : NonnegOnQ 0 (3675/2048) := nonnegOn_union 0 (225/128) (3675/2048) h136 n0137
  have h138 : NonnegOnQ 0 (1875/1024) := nonnegOn_union 0 (3675/2048) (1875/1024) h137 n0138
  have h139 : NonnegOnQ 0 (3825/2048) := nonnegOn_union 0 (1875/1024) (3825/2048) h138 n0139
  have h140 : NonnegOnQ 0 (975/512) := nonnegOn_union 0 (3825/2048) (975/512) h139 n0140
  have h141 : NonnegOnQ 0 (3975/2048) := nonnegOn_union 0 (975/512) (3975/2048) h140 n0141
  have h142 : NonnegOnQ 0 (2025/1024) := nonnegOn_union 0 (3975/2048) (2025/1024) h141 n0142
  exact h142

end AEGIS.RHKreinTrigramAdaptiveV1
