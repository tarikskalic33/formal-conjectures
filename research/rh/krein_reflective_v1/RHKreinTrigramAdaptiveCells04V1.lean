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
import RHKreinTrigramAdaptiveCells03V1

set_option autoImplicit false
noncomputable section
namespace AEGIS.RHKreinTrigramAdaptiveV1
open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinCellBatchV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinFirstCellV1
open AEGIS.RHKreinSecondCellReductionV1

theorem c0143 : checkPiece pa19 (2025/1024) 0 (2025/1024) (4125/2048) = true := by decide +kernel
theorem n0143 : NonnegOnQ (2025/1024) (4125/2048) :=
  nonnegOn_of_checkPiece_zero (2025/1024) (4125/2048) (by norm_num) c0143

theorem c0144 : checkPiece pa19 (4125/2048) 0 (4125/2048) (525/256) = true := by decide +kernel
theorem n0144 : NonnegOnQ (4125/2048) (525/256) :=
  nonnegOn_of_checkPiece_zero (4125/2048) (525/256) (by norm_num) c0144

theorem c0145 : checkPiece pa19 (525/256) 0 (525/256) (4275/2048) = true := by decide +kernel
theorem n0145 : NonnegOnQ (525/256) (4275/2048) :=
  nonnegOn_of_checkPiece_zero (525/256) (4275/2048) (by norm_num) c0145

theorem c0146 : checkPiece pa19 (4275/2048) 0 (4275/2048) (2175/1024) = true := by decide +kernel
theorem n0146 : NonnegOnQ (4275/2048) (2175/1024) :=
  nonnegOn_of_checkPiece_zero (4275/2048) (2175/1024) (by norm_num) c0146

theorem c0147 : checkPiece pa19 (2175/1024) 0 (2175/1024) (4425/2048) = true := by decide +kernel
theorem n0147 : NonnegOnQ (2175/1024) (4425/2048) :=
  nonnegOn_of_checkPiece_zero (2175/1024) (4425/2048) (by norm_num) c0147

theorem c0148 : checkPiece pa19 (4425/2048) 0 (4425/2048) (1125/512) = true := by decide +kernel
theorem n0148 : NonnegOnQ (4425/2048) (1125/512) :=
  nonnegOn_of_checkPiece_zero (4425/2048) (1125/512) (by norm_num) c0148

theorem c0149 : checkPiece pa19 (1125/512) 0 (1125/512) (4575/2048) = true := by decide +kernel
theorem n0149 : NonnegOnQ (1125/512) (4575/2048) :=
  nonnegOn_of_checkPiece_zero (1125/512) (4575/2048) (by norm_num) c0149

theorem c0150 : checkPiece pa19 (4575/2048) 0 (4575/2048) (2325/1024) = true := by decide +kernel
theorem n0150 : NonnegOnQ (4575/2048) (2325/1024) :=
  nonnegOn_of_checkPiece_zero (4575/2048) (2325/1024) (by norm_num) c0150

theorem c0151 : checkPiece pa19 (2325/1024) 0 (2325/1024) (4725/2048) = true := by decide +kernel
theorem n0151 : NonnegOnQ (2325/1024) (4725/2048) :=
  nonnegOn_of_checkPiece_zero (2325/1024) (4725/2048) (by norm_num) c0151

theorem c0152 : checkPiece pa19 (4725/2048) 0 (4725/2048) (75/32) = true := by decide +kernel
theorem n0152 : NonnegOnQ (4725/2048) (75/32) :=
  nonnegOn_of_checkPiece_zero (4725/2048) (75/32) (by norm_num) c0152

theorem c0153 : checkPiece pa19 (75/32) 0 (75/32) (4875/2048) = true := by decide +kernel
theorem n0153 : NonnegOnQ (75/32) (4875/2048) :=
  nonnegOn_of_checkPiece_zero (75/32) (4875/2048) (by norm_num) c0153

theorem c0154 : checkPiece pa19 (4875/2048) 0 (4875/2048) (2475/1024) = true := by decide +kernel
theorem n0154 : NonnegOnQ (4875/2048) (2475/1024) :=
  nonnegOn_of_checkPiece_zero (4875/2048) (2475/1024) (by norm_num) c0154

theorem c0155 : checkPiece pa19 (2475/1024) 0 (2475/1024) (1275/512) = true := by decide +kernel
theorem n0155 : NonnegOnQ (2475/1024) (1275/512) :=
  nonnegOn_of_checkPiece_zero (2475/1024) (1275/512) (by norm_num) c0155

theorem c0156 : checkPiece pa19 (1275/512) 0 (1275/512) (2625/1024) = true := by decide +kernel
theorem n0156 : NonnegOnQ (1275/512) (2625/1024) :=
  nonnegOn_of_checkPiece_zero (1275/512) (2625/1024) (by norm_num) c0156

theorem c0157 : checkPiece pa19 (2625/1024) 0 (2625/1024) (675/256) = true := by decide +kernel
theorem n0157 : NonnegOnQ (2625/1024) (675/256) :=
  nonnegOn_of_checkPiece_zero (2625/1024) (675/256) (by norm_num) c0157

theorem c0158 : checkPiece pa19 (675/256) 0 (675/256) (2775/1024) = true := by decide +kernel
theorem n0158 : NonnegOnQ (675/256) (2775/1024) :=
  nonnegOn_of_checkPiece_zero (675/256) (2775/1024) (by norm_num) c0158

theorem c0159 : checkPiece pa19 (2775/1024) 0 (2775/1024) (1425/512) = true := by decide +kernel
theorem n0159 : NonnegOnQ (2775/1024) (1425/512) :=
  nonnegOn_of_checkPiece_zero (2775/1024) (1425/512) (by norm_num) c0159

theorem c0160 : checkPiece pa19 (1425/512) 0 (1425/512) (2925/1024) = true := by decide +kernel
theorem n0160 : NonnegOnQ (1425/512) (2925/1024) :=
  nonnegOn_of_checkPiece_zero (1425/512) (2925/1024) (by norm_num) c0160

theorem c0161 : checkPiece pa19 (2925/1024) 0 (2925/1024) (375/128) = true := by decide +kernel
theorem n0161 : NonnegOnQ (2925/1024) (375/128) :=
  nonnegOn_of_checkPiece_zero (2925/1024) (375/128) (by norm_num) c0161

theorem c0162 : checkPiece pa19 (375/128) 0 (375/128) (3075/1024) = true := by decide +kernel
theorem n0162 : NonnegOnQ (375/128) (3075/1024) :=
  nonnegOn_of_checkPiece_zero (375/128) (3075/1024) (by norm_num) c0162

theorem c0163 : checkPiece pa19 (3075/1024) 0 (3075/1024) (1575/512) = true := by decide +kernel
theorem n0163 : NonnegOnQ (3075/1024) (1575/512) :=
  nonnegOn_of_checkPiece_zero (3075/1024) (1575/512) (by norm_num) c0163

theorem c0164 : checkPiece pa19 (1575/512) 0 (1575/512) (3225/1024) = true := by decide +kernel
theorem n0164 : NonnegOnQ (1575/512) (3225/1024) :=
  nonnegOn_of_checkPiece_zero (1575/512) (3225/1024) (by norm_num) c0164

theorem c0165 : checkPiece pa19 (3225/1024) 0 (3225/1024) (825/256) = true := by decide +kernel
theorem n0165 : NonnegOnQ (3225/1024) (825/256) :=
  nonnegOn_of_checkPiece_zero (3225/1024) (825/256) (by norm_num) c0165

theorem c0166 : checkPiece pa19 (825/256) 0 (825/256) (3375/1024) = true := by decide +kernel
theorem n0166 : NonnegOnQ (825/256) (3375/1024) :=
  nonnegOn_of_checkPiece_zero (825/256) (3375/1024) (by norm_num) c0166

theorem c0167 : checkPiece pa19 (3375/1024) 0 (3375/1024) (1725/512) = true := by decide +kernel
theorem n0167 : NonnegOnQ (3375/1024) (1725/512) :=
  nonnegOn_of_checkPiece_zero (3375/1024) (1725/512) (by norm_num) c0167

theorem c0168 : checkPiece pa19 (1725/512) 0 (1725/512) (3525/1024) = true := by decide +kernel
theorem n0168 : NonnegOnQ (1725/512) (3525/1024) :=
  nonnegOn_of_checkPiece_zero (1725/512) (3525/1024) (by norm_num) c0168

theorem c0169 : checkPiece pa19 (3525/1024) 0 (3525/1024) (225/64) = true := by decide +kernel
theorem n0169 : NonnegOnQ (3525/1024) (225/64) :=
  nonnegOn_of_checkPiece_zero (3525/1024) (225/64) (by norm_num) c0169

theorem c0170 : checkPiece pa19 (225/64) 0 (225/64) (3675/1024) = true := by decide +kernel
theorem n0170 : NonnegOnQ (225/64) (3675/1024) :=
  nonnegOn_of_checkPiece_zero (225/64) (3675/1024) (by norm_num) c0170

theorem c0171 : checkPiece pa19 (3675/1024) 0 (3675/1024) (1875/512) = true := by decide +kernel
theorem n0171 : NonnegOnQ (3675/1024) (1875/512) :=
  nonnegOn_of_checkPiece_zero (3675/1024) (1875/512) (by norm_num) c0171

theorem c0172 : checkPiece pa19 (1875/512) 0 (1875/512) (3825/1024) = true := by decide +kernel
theorem n0172 : NonnegOnQ (1875/512) (3825/1024) :=
  nonnegOn_of_checkPiece_zero (1875/512) (3825/1024) (by norm_num) c0172

theorem c0173 : checkPiece pa19 (3825/1024) 0 (3825/1024) (975/256) = true := by decide +kernel
theorem n0173 : NonnegOnQ (3825/1024) (975/256) :=
  nonnegOn_of_checkPiece_zero (3825/1024) (975/256) (by norm_num) c0173

theorem c0174 : checkPiece pa19 (975/256) 0 (975/256) (3975/1024) = true := by decide +kernel
theorem n0174 : NonnegOnQ (975/256) (3975/1024) :=
  nonnegOn_of_checkPiece_zero (975/256) (3975/1024) (by norm_num) c0174

theorem c0175 : checkPiece pa19 (3975/1024) 0 (3975/1024) (2025/512) = true := by decide +kernel
theorem n0175 : NonnegOnQ (3975/1024) (2025/512) :=
  nonnegOn_of_checkPiece_zero (3975/1024) (2025/512) (by norm_num) c0175

theorem c0176 : checkPiece pa19 (2025/512) 0 (2025/512) (4125/1024) = true := by decide +kernel
theorem n0176 : NonnegOnQ (2025/512) (4125/1024) :=
  nonnegOn_of_checkPiece_zero (2025/512) (4125/1024) (by norm_num) c0176

theorem c0177 : checkPiece pa19 (4125/1024) 0 (4125/1024) (525/128) = true := by decide +kernel
theorem n0177 : NonnegOnQ (4125/1024) (525/128) :=
  nonnegOn_of_checkPiece_zero (4125/1024) (525/128) (by norm_num) c0177

theorem c0178 : checkPiece pa19 (525/128) 0 (525/128) (4275/1024) = true := by decide +kernel
theorem n0178 : NonnegOnQ (525/128) (4275/1024) :=
  nonnegOn_of_checkPiece_zero (525/128) (4275/1024) (by norm_num) c0178

theorem c0179 : checkPiece pa19 (4275/1024) 0 (4275/1024) (2175/512) = true := by decide +kernel
theorem n0179 : NonnegOnQ (4275/1024) (2175/512) :=
  nonnegOn_of_checkPiece_zero (4275/1024) (2175/512) (by norm_num) c0179

theorem c0180 : checkPiece pa19 (2175/512) 0 (2175/512) (4425/1024) = true := by decide +kernel
theorem n0180 : NonnegOnQ (2175/512) (4425/1024) :=
  nonnegOn_of_checkPiece_zero (2175/512) (4425/1024) (by norm_num) c0180

theorem c0181 : checkPiece pa19 (4425/1024) 0 (4425/1024) (1125/256) = true := by decide +kernel
theorem n0181 : NonnegOnQ (4425/1024) (1125/256) :=
  nonnegOn_of_checkPiece_zero (4425/1024) (1125/256) (by norm_num) c0181

theorem c0182 : checkPiece pa19 (1125/256) 0 (1125/256) (4575/1024) = true := by decide +kernel
theorem n0182 : NonnegOnQ (1125/256) (4575/1024) :=
  nonnegOn_of_checkPiece_zero (1125/256) (4575/1024) (by norm_num) c0182

theorem c0183 : checkPiece pa19 (4575/1024) 0 (4575/1024) (2325/512) = true := by decide +kernel
theorem n0183 : NonnegOnQ (4575/1024) (2325/512) :=
  nonnegOn_of_checkPiece_zero (4575/1024) (2325/512) (by norm_num) c0183

theorem c0184 : checkPiece pa19 (2325/512) 0 (2325/512) (4725/1024) = true := by decide +kernel
theorem n0184 : NonnegOnQ (2325/512) (4725/1024) :=
  nonnegOn_of_checkPiece_zero (2325/512) (4725/1024) (by norm_num) c0184

theorem c0185 : checkPiece pa19 (4725/1024) 0 (4725/1024) (75/16) = true := by decide +kernel
theorem n0185 : NonnegOnQ (4725/1024) (75/16) :=
  nonnegOn_of_checkPiece_zero (4725/1024) (75/16) (by norm_num) c0185

theorem c0186 : checkPiece pa19 (75/16) 0 (75/16) (2475/512) = true := by decide +kernel
theorem n0186 : NonnegOnQ (75/16) (2475/512) :=
  nonnegOn_of_checkPiece_zero (75/16) (2475/512) (by norm_num) c0186

theorem c0187 : checkPiece pa19 (2475/512) 0 (2475/512) (1275/256) = true := by decide +kernel
theorem n0187 : NonnegOnQ (2475/512) (1275/256) :=
  nonnegOn_of_checkPiece_zero (2475/512) (1275/256) (by norm_num) c0187

theorem c0188 : checkPiece pa19 (1275/256) 0 (1275/256) (2625/512) = true := by decide +kernel
theorem n0188 : NonnegOnQ (1275/256) (2625/512) :=
  nonnegOn_of_checkPiece_zero (1275/256) (2625/512) (by norm_num) c0188

theorem c0189 : checkPiece pa19 (2625/512) 0 (2625/512) (675/128) = true := by decide +kernel
theorem n0189 : NonnegOnQ (2625/512) (675/128) :=
  nonnegOn_of_checkPiece_zero (2625/512) (675/128) (by norm_num) c0189

/- Original contiguous interval fold, staged to bound Lean memory use. -/
set_option maxRecDepth 4096 in
theorem foldTo0189 : NonnegOnQ 0 (675/128) := by
  have h142 := foldTo0142
  have h143 : NonnegOnQ 0 (4125/2048) := nonnegOn_union 0 (2025/1024) (4125/2048) h142 n0143
  have h144 : NonnegOnQ 0 (525/256) := nonnegOn_union 0 (4125/2048) (525/256) h143 n0144
  have h145 : NonnegOnQ 0 (4275/2048) := nonnegOn_union 0 (525/256) (4275/2048) h144 n0145
  have h146 : NonnegOnQ 0 (2175/1024) := nonnegOn_union 0 (4275/2048) (2175/1024) h145 n0146
  have h147 : NonnegOnQ 0 (4425/2048) := nonnegOn_union 0 (2175/1024) (4425/2048) h146 n0147
  have h148 : NonnegOnQ 0 (1125/512) := nonnegOn_union 0 (4425/2048) (1125/512) h147 n0148
  have h149 : NonnegOnQ 0 (4575/2048) := nonnegOn_union 0 (1125/512) (4575/2048) h148 n0149
  have h150 : NonnegOnQ 0 (2325/1024) := nonnegOn_union 0 (4575/2048) (2325/1024) h149 n0150
  have h151 : NonnegOnQ 0 (4725/2048) := nonnegOn_union 0 (2325/1024) (4725/2048) h150 n0151
  have h152 : NonnegOnQ 0 (75/32) := nonnegOn_union 0 (4725/2048) (75/32) h151 n0152
  have h153 : NonnegOnQ 0 (4875/2048) := nonnegOn_union 0 (75/32) (4875/2048) h152 n0153
  have h154 : NonnegOnQ 0 (2475/1024) := nonnegOn_union 0 (4875/2048) (2475/1024) h153 n0154
  have h155 : NonnegOnQ 0 (1275/512) := nonnegOn_union 0 (2475/1024) (1275/512) h154 n0155
  have h156 : NonnegOnQ 0 (2625/1024) := nonnegOn_union 0 (1275/512) (2625/1024) h155 n0156
  have h157 : NonnegOnQ 0 (675/256) := nonnegOn_union 0 (2625/1024) (675/256) h156 n0157
  have h158 : NonnegOnQ 0 (2775/1024) := nonnegOn_union 0 (675/256) (2775/1024) h157 n0158
  have h159 : NonnegOnQ 0 (1425/512) := nonnegOn_union 0 (2775/1024) (1425/512) h158 n0159
  have h160 : NonnegOnQ 0 (2925/1024) := nonnegOn_union 0 (1425/512) (2925/1024) h159 n0160
  have h161 : NonnegOnQ 0 (375/128) := nonnegOn_union 0 (2925/1024) (375/128) h160 n0161
  have h162 : NonnegOnQ 0 (3075/1024) := nonnegOn_union 0 (375/128) (3075/1024) h161 n0162
  have h163 : NonnegOnQ 0 (1575/512) := nonnegOn_union 0 (3075/1024) (1575/512) h162 n0163
  have h164 : NonnegOnQ 0 (3225/1024) := nonnegOn_union 0 (1575/512) (3225/1024) h163 n0164
  have h165 : NonnegOnQ 0 (825/256) := nonnegOn_union 0 (3225/1024) (825/256) h164 n0165
  have h166 : NonnegOnQ 0 (3375/1024) := nonnegOn_union 0 (825/256) (3375/1024) h165 n0166
  have h167 : NonnegOnQ 0 (1725/512) := nonnegOn_union 0 (3375/1024) (1725/512) h166 n0167
  have h168 : NonnegOnQ 0 (3525/1024) := nonnegOn_union 0 (1725/512) (3525/1024) h167 n0168
  have h169 : NonnegOnQ 0 (225/64) := nonnegOn_union 0 (3525/1024) (225/64) h168 n0169
  have h170 : NonnegOnQ 0 (3675/1024) := nonnegOn_union 0 (225/64) (3675/1024) h169 n0170
  have h171 : NonnegOnQ 0 (1875/512) := nonnegOn_union 0 (3675/1024) (1875/512) h170 n0171
  have h172 : NonnegOnQ 0 (3825/1024) := nonnegOn_union 0 (1875/512) (3825/1024) h171 n0172
  have h173 : NonnegOnQ 0 (975/256) := nonnegOn_union 0 (3825/1024) (975/256) h172 n0173
  have h174 : NonnegOnQ 0 (3975/1024) := nonnegOn_union 0 (975/256) (3975/1024) h173 n0174
  have h175 : NonnegOnQ 0 (2025/512) := nonnegOn_union 0 (3975/1024) (2025/512) h174 n0175
  have h176 : NonnegOnQ 0 (4125/1024) := nonnegOn_union 0 (2025/512) (4125/1024) h175 n0176
  have h177 : NonnegOnQ 0 (525/128) := nonnegOn_union 0 (4125/1024) (525/128) h176 n0177
  have h178 : NonnegOnQ 0 (4275/1024) := nonnegOn_union 0 (525/128) (4275/1024) h177 n0178
  have h179 : NonnegOnQ 0 (2175/512) := nonnegOn_union 0 (4275/1024) (2175/512) h178 n0179
  have h180 : NonnegOnQ 0 (4425/1024) := nonnegOn_union 0 (2175/512) (4425/1024) h179 n0180
  have h181 : NonnegOnQ 0 (1125/256) := nonnegOn_union 0 (4425/1024) (1125/256) h180 n0181
  have h182 : NonnegOnQ 0 (4575/1024) := nonnegOn_union 0 (1125/256) (4575/1024) h181 n0182
  have h183 : NonnegOnQ 0 (2325/512) := nonnegOn_union 0 (4575/1024) (2325/512) h182 n0183
  have h184 : NonnegOnQ 0 (4725/1024) := nonnegOn_union 0 (2325/512) (4725/1024) h183 n0184
  have h185 : NonnegOnQ 0 (75/16) := nonnegOn_union 0 (4725/1024) (75/16) h184 n0185
  have h186 : NonnegOnQ 0 (2475/512) := nonnegOn_union 0 (75/16) (2475/512) h185 n0186
  have h187 : NonnegOnQ 0 (1275/256) := nonnegOn_union 0 (2475/512) (1275/256) h186 n0187
  have h188 : NonnegOnQ 0 (2625/512) := nonnegOn_union 0 (1275/256) (2625/512) h187 n0188
  have h189 : NonnegOnQ 0 (675/128) := nonnegOn_union 0 (2625/512) (675/128) h188 n0189
  exact h189

end AEGIS.RHKreinTrigramAdaptiveV1
