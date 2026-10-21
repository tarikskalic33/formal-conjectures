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
/- Complete staged arithmetic for the actual source-input join. -/
import CvSCachedPointV1
import CvSSourceECacheV1
import CvSSourceXCacheV1
import CvSSourceLambdaCacheV1
import CvSFullCachedTableV1
import CvSSourceProduct0
import CvSSourceProduct1
import CvSSourceProduct2
import CvSSourceProduct3
import CvSSourceProduct4
import CvSSourceProduct5
import CvSSourceProduct6
import CvSSourceProduct7
import CvSSourceProduct8
import CvSSourceProduct9
import CvSSourceProduct10
import CvSSourceProduct11
import CvSSourceProduct12
import CvSSourceProduct13
import CvSSourceProduct14
import CvSSourceProduct15
import CvSSourceProduct16
import CvSSourceProduct17
import CvSSourceProduct18
import CvSSourceProduct19
import CvSSourceProduct20
import CvSSourceProduct21
import CvSSourceProduct22
import CvSSourceProduct23
import CvSSourceProduct24
import CvSSourceProduct25
import CvSSourceProduct26
import CvSSourceProduct27
import CvSSourceProduct28
import CvSSourceProduct29
import CvSSourceProduct30
import CvSSourceProduct31
import CvSSourceProduct32
import CvSSourceProduct33
import CvSSourceProduct34
import CvSSourceProduct35
import CvSSourceProduct36
import CvSSourceProduct37
import CvSSourceProduct38
import CvSSourceProduct39
import CvSSourceProduct40
import CvSSourceProduct41
import CvSSourceProduct42
import CvSSourceProduct43
import CvSSourceProduct44
import CvSSourceProduct45
import CvSSourceProduct46
import CvSSourceProduct47
import CvSSourceProduct48
import CvSSourceProduct49
import CvSSourceProduct50
import CvSSourceProduct51
import CvSSourceProduct52
import CvSSourceProduct53
import CvSSourceProduct54
import CvSSourceProduct55
import CvSSourceProduct56
import CvSSourceProduct57
import CvSSourceProduct58
import CvSSourceProduct59
import CvSSourceProduct60
import CvSSourceProduct61
import CvSSourceProduct62
import CvSSourceProduct63
import CvSSourceProduct64
import CvSSourceProduct65
import CvSSourceProduct66
import CvSSourceProduct67
import CvSSourceProduct68
import CvSSourceProduct69
import CvSSourceProduct70
import CvSSourceProduct71
import CvSSourceProduct72
import CvSSourceProduct73
import CvSSourceProduct74
import CvSSourceProduct75
import CvSSourceProduct76
import CvSSourceProduct77
import CvSSourceProduct78
import CvSSourceProduct79
import CvSSourceProduct80
import CvSSourceProduct81
import CvSSourceProduct82
import CvSSourceProduct83
import CvSSourceProduct84
import CvSSourceProduct85
import CvSSourceProduct86
import CvSSourceProduct87
import CvSSourceProduct88
import CvSSourceProduct89
import CvSSourceProduct90
import CvSSourceProduct91
import CvSSourceProduct92
import CvSSourceProduct93
import CvSSourceProduct94
import CvSSourceProduct95
import CvSSourceProduct96
import CvSSourceProduct97
import CvSSourceProduct98
import CvSSourceProduct99
import CvSSourceProduct100
import CvSSourceProduct101
import CvSSourceProduct102
import CvSSourceProduct103
import CvSSourceProduct104
import CvSSourceProduct105
import CvSSourceProduct106
import CvSSourceProduct107
import CvSSourceProduct108
import CvSSourceProduct109
import CvSSourceProduct110
import CvSSourceProduct111
import CvSSourceProduct112
import CvSSourceProduct113
import CvSSourceProduct114
import CvSSourceProduct115
import CvSSourceProduct116
import CvSSourceProduct117
import CvSSourceProduct118
import CvSSourceProduct119
import CvSSourceProduct120
import CvSSourceProduct121
import CvSSourceProduct122
import CvSSourceProduct123
import CvSSourceProduct124
import CvSSourceProduct125
import CvSSourceProduct126
import CvSSourceProduct127
import CvSSourceProduct128
import CvSSourceProduct129
import CvSSourceProduct130
import CvSSourceProduct131
import CvSSourceProduct132
import CvSSourceProduct133
import CvSSourceProduct134
import CvSSourceProduct135
import CvSSourceProduct136
import CvSSourceProduct137
import CvSSourceProduct138
import Mathlib.Tactic.FinCases
open scoped BigOperators
namespace AEGIS.CvSSourceProductAllV1
open AEGIS.RHFixIntervalV1 AEGIS.CvSCachedColumnV1
open AEGIS.CvSCachedSourceProductV1 AEGIS.CvSCachedPointV1
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

def inputColumn (i : Fin 139) := AEGIS.CvSFullCachedTableV1.column i.val
def eRow (r : Fin 301) : Vector 141 := AEGIS.CvSSourceECacheV1.rows.getD r.val
  AEGIS.CvSSourceERows0.row0
def xRow (k : Fin 141) : Vector 139 := AEGIS.CvSSourceXCacheV1.rows.getD k.val
  AEGIS.CvSSourceXRows0.row0
def lambdaColumn (i : Fin 139) : Vector 139 := AEGIS.CvSSourceLambdaCacheV1.rows.getD i.val
  AEGIS.CvSSourceLambdaRows0.row0
def lambdaBox (j i : Fin 139) : Iv := (lambdaColumn i).values.getD j.val ⟨0, 0⟩
noncomputable def lambdaReal (j i : Fin 139) : ℝ := ((lambdaBox j i).lo : ℝ) / 2^96
def ys : List (List Iv) := [AEGIS.CvSSourceProduct0.Y, AEGIS.CvSSourceProduct1.Y, AEGIS.CvSSourceProduct2.Y, AEGIS.CvSSourceProduct3.Y, AEGIS.CvSSourceProduct4.Y, AEGIS.CvSSourceProduct5.Y, AEGIS.CvSSourceProduct6.Y, AEGIS.CvSSourceProduct7.Y, AEGIS.CvSSourceProduct8.Y, AEGIS.CvSSourceProduct9.Y, AEGIS.CvSSourceProduct10.Y, AEGIS.CvSSourceProduct11.Y, AEGIS.CvSSourceProduct12.Y, AEGIS.CvSSourceProduct13.Y, AEGIS.CvSSourceProduct14.Y, AEGIS.CvSSourceProduct15.Y, AEGIS.CvSSourceProduct16.Y, AEGIS.CvSSourceProduct17.Y, AEGIS.CvSSourceProduct18.Y, AEGIS.CvSSourceProduct19.Y, AEGIS.CvSSourceProduct20.Y, AEGIS.CvSSourceProduct21.Y, AEGIS.CvSSourceProduct22.Y, AEGIS.CvSSourceProduct23.Y, AEGIS.CvSSourceProduct24.Y, AEGIS.CvSSourceProduct25.Y, AEGIS.CvSSourceProduct26.Y, AEGIS.CvSSourceProduct27.Y, AEGIS.CvSSourceProduct28.Y, AEGIS.CvSSourceProduct29.Y, AEGIS.CvSSourceProduct30.Y, AEGIS.CvSSourceProduct31.Y, AEGIS.CvSSourceProduct32.Y, AEGIS.CvSSourceProduct33.Y, AEGIS.CvSSourceProduct34.Y, AEGIS.CvSSourceProduct35.Y, AEGIS.CvSSourceProduct36.Y, AEGIS.CvSSourceProduct37.Y, AEGIS.CvSSourceProduct38.Y, AEGIS.CvSSourceProduct39.Y, AEGIS.CvSSourceProduct40.Y, AEGIS.CvSSourceProduct41.Y, AEGIS.CvSSourceProduct42.Y, AEGIS.CvSSourceProduct43.Y, AEGIS.CvSSourceProduct44.Y, AEGIS.CvSSourceProduct45.Y, AEGIS.CvSSourceProduct46.Y, AEGIS.CvSSourceProduct47.Y, AEGIS.CvSSourceProduct48.Y, AEGIS.CvSSourceProduct49.Y, AEGIS.CvSSourceProduct50.Y, AEGIS.CvSSourceProduct51.Y, AEGIS.CvSSourceProduct52.Y, AEGIS.CvSSourceProduct53.Y, AEGIS.CvSSourceProduct54.Y, AEGIS.CvSSourceProduct55.Y, AEGIS.CvSSourceProduct56.Y, AEGIS.CvSSourceProduct57.Y, AEGIS.CvSSourceProduct58.Y, AEGIS.CvSSourceProduct59.Y, AEGIS.CvSSourceProduct60.Y, AEGIS.CvSSourceProduct61.Y, AEGIS.CvSSourceProduct62.Y, AEGIS.CvSSourceProduct63.Y, AEGIS.CvSSourceProduct64.Y, AEGIS.CvSSourceProduct65.Y, AEGIS.CvSSourceProduct66.Y, AEGIS.CvSSourceProduct67.Y, AEGIS.CvSSourceProduct68.Y, AEGIS.CvSSourceProduct69.Y, AEGIS.CvSSourceProduct70.Y, AEGIS.CvSSourceProduct71.Y, AEGIS.CvSSourceProduct72.Y, AEGIS.CvSSourceProduct73.Y, AEGIS.CvSSourceProduct74.Y, AEGIS.CvSSourceProduct75.Y, AEGIS.CvSSourceProduct76.Y, AEGIS.CvSSourceProduct77.Y, AEGIS.CvSSourceProduct78.Y, AEGIS.CvSSourceProduct79.Y, AEGIS.CvSSourceProduct80.Y, AEGIS.CvSSourceProduct81.Y, AEGIS.CvSSourceProduct82.Y, AEGIS.CvSSourceProduct83.Y, AEGIS.CvSSourceProduct84.Y, AEGIS.CvSSourceProduct85.Y, AEGIS.CvSSourceProduct86.Y, AEGIS.CvSSourceProduct87.Y, AEGIS.CvSSourceProduct88.Y, AEGIS.CvSSourceProduct89.Y, AEGIS.CvSSourceProduct90.Y, AEGIS.CvSSourceProduct91.Y, AEGIS.CvSSourceProduct92.Y, AEGIS.CvSSourceProduct93.Y, AEGIS.CvSSourceProduct94.Y, AEGIS.CvSSourceProduct95.Y, AEGIS.CvSSourceProduct96.Y, AEGIS.CvSSourceProduct97.Y, AEGIS.CvSSourceProduct98.Y, AEGIS.CvSSourceProduct99.Y, AEGIS.CvSSourceProduct100.Y, AEGIS.CvSSourceProduct101.Y, AEGIS.CvSSourceProduct102.Y, AEGIS.CvSSourceProduct103.Y, AEGIS.CvSSourceProduct104.Y, AEGIS.CvSSourceProduct105.Y, AEGIS.CvSSourceProduct106.Y, AEGIS.CvSSourceProduct107.Y, AEGIS.CvSSourceProduct108.Y, AEGIS.CvSSourceProduct109.Y, AEGIS.CvSSourceProduct110.Y, AEGIS.CvSSourceProduct111.Y, AEGIS.CvSSourceProduct112.Y, AEGIS.CvSSourceProduct113.Y, AEGIS.CvSSourceProduct114.Y, AEGIS.CvSSourceProduct115.Y, AEGIS.CvSSourceProduct116.Y, AEGIS.CvSSourceProduct117.Y, AEGIS.CvSSourceProduct118.Y, AEGIS.CvSSourceProduct119.Y, AEGIS.CvSSourceProduct120.Y, AEGIS.CvSSourceProduct121.Y, AEGIS.CvSSourceProduct122.Y, AEGIS.CvSSourceProduct123.Y, AEGIS.CvSSourceProduct124.Y, AEGIS.CvSSourceProduct125.Y, AEGIS.CvSSourceProduct126.Y, AEGIS.CvSSourceProduct127.Y, AEGIS.CvSSourceProduct128.Y, AEGIS.CvSSourceProduct129.Y, AEGIS.CvSSourceProduct130.Y, AEGIS.CvSSourceProduct131.Y, AEGIS.CvSSourceProduct132.Y, AEGIS.CvSSourceProduct133.Y, AEGIS.CvSSourceProduct134.Y, AEGIS.CvSSourceProduct135.Y, AEGIS.CvSSourceProduct136.Y, AEGIS.CvSSourceProduct137.Y, AEGIS.CvSSourceProduct138.Y]
def inners : List (List Iv) := [AEGIS.CvSSourceProduct0.inner, AEGIS.CvSSourceProduct1.inner, AEGIS.CvSSourceProduct2.inner, AEGIS.CvSSourceProduct3.inner, AEGIS.CvSSourceProduct4.inner, AEGIS.CvSSourceProduct5.inner, AEGIS.CvSSourceProduct6.inner, AEGIS.CvSSourceProduct7.inner, AEGIS.CvSSourceProduct8.inner, AEGIS.CvSSourceProduct9.inner, AEGIS.CvSSourceProduct10.inner, AEGIS.CvSSourceProduct11.inner, AEGIS.CvSSourceProduct12.inner, AEGIS.CvSSourceProduct13.inner, AEGIS.CvSSourceProduct14.inner, AEGIS.CvSSourceProduct15.inner, AEGIS.CvSSourceProduct16.inner, AEGIS.CvSSourceProduct17.inner, AEGIS.CvSSourceProduct18.inner, AEGIS.CvSSourceProduct19.inner, AEGIS.CvSSourceProduct20.inner, AEGIS.CvSSourceProduct21.inner, AEGIS.CvSSourceProduct22.inner, AEGIS.CvSSourceProduct23.inner, AEGIS.CvSSourceProduct24.inner, AEGIS.CvSSourceProduct25.inner, AEGIS.CvSSourceProduct26.inner, AEGIS.CvSSourceProduct27.inner, AEGIS.CvSSourceProduct28.inner, AEGIS.CvSSourceProduct29.inner, AEGIS.CvSSourceProduct30.inner, AEGIS.CvSSourceProduct31.inner, AEGIS.CvSSourceProduct32.inner, AEGIS.CvSSourceProduct33.inner, AEGIS.CvSSourceProduct34.inner, AEGIS.CvSSourceProduct35.inner, AEGIS.CvSSourceProduct36.inner, AEGIS.CvSSourceProduct37.inner, AEGIS.CvSSourceProduct38.inner, AEGIS.CvSSourceProduct39.inner, AEGIS.CvSSourceProduct40.inner, AEGIS.CvSSourceProduct41.inner, AEGIS.CvSSourceProduct42.inner, AEGIS.CvSSourceProduct43.inner, AEGIS.CvSSourceProduct44.inner, AEGIS.CvSSourceProduct45.inner, AEGIS.CvSSourceProduct46.inner, AEGIS.CvSSourceProduct47.inner, AEGIS.CvSSourceProduct48.inner, AEGIS.CvSSourceProduct49.inner, AEGIS.CvSSourceProduct50.inner, AEGIS.CvSSourceProduct51.inner, AEGIS.CvSSourceProduct52.inner, AEGIS.CvSSourceProduct53.inner, AEGIS.CvSSourceProduct54.inner, AEGIS.CvSSourceProduct55.inner, AEGIS.CvSSourceProduct56.inner, AEGIS.CvSSourceProduct57.inner, AEGIS.CvSSourceProduct58.inner, AEGIS.CvSSourceProduct59.inner, AEGIS.CvSSourceProduct60.inner, AEGIS.CvSSourceProduct61.inner, AEGIS.CvSSourceProduct62.inner, AEGIS.CvSSourceProduct63.inner, AEGIS.CvSSourceProduct64.inner, AEGIS.CvSSourceProduct65.inner, AEGIS.CvSSourceProduct66.inner, AEGIS.CvSSourceProduct67.inner, AEGIS.CvSSourceProduct68.inner, AEGIS.CvSSourceProduct69.inner, AEGIS.CvSSourceProduct70.inner, AEGIS.CvSSourceProduct71.inner, AEGIS.CvSSourceProduct72.inner, AEGIS.CvSSourceProduct73.inner, AEGIS.CvSSourceProduct74.inner, AEGIS.CvSSourceProduct75.inner, AEGIS.CvSSourceProduct76.inner, AEGIS.CvSSourceProduct77.inner, AEGIS.CvSSourceProduct78.inner, AEGIS.CvSSourceProduct79.inner, AEGIS.CvSSourceProduct80.inner, AEGIS.CvSSourceProduct81.inner, AEGIS.CvSSourceProduct82.inner, AEGIS.CvSSourceProduct83.inner, AEGIS.CvSSourceProduct84.inner, AEGIS.CvSSourceProduct85.inner, AEGIS.CvSSourceProduct86.inner, AEGIS.CvSSourceProduct87.inner, AEGIS.CvSSourceProduct88.inner, AEGIS.CvSSourceProduct89.inner, AEGIS.CvSSourceProduct90.inner, AEGIS.CvSSourceProduct91.inner, AEGIS.CvSSourceProduct92.inner, AEGIS.CvSSourceProduct93.inner, AEGIS.CvSSourceProduct94.inner, AEGIS.CvSSourceProduct95.inner, AEGIS.CvSSourceProduct96.inner, AEGIS.CvSSourceProduct97.inner, AEGIS.CvSSourceProduct98.inner, AEGIS.CvSSourceProduct99.inner, AEGIS.CvSSourceProduct100.inner, AEGIS.CvSSourceProduct101.inner, AEGIS.CvSSourceProduct102.inner, AEGIS.CvSSourceProduct103.inner, AEGIS.CvSSourceProduct104.inner, AEGIS.CvSSourceProduct105.inner, AEGIS.CvSSourceProduct106.inner, AEGIS.CvSSourceProduct107.inner, AEGIS.CvSSourceProduct108.inner, AEGIS.CvSSourceProduct109.inner, AEGIS.CvSSourceProduct110.inner, AEGIS.CvSSourceProduct111.inner, AEGIS.CvSSourceProduct112.inner, AEGIS.CvSSourceProduct113.inner, AEGIS.CvSSourceProduct114.inner, AEGIS.CvSSourceProduct115.inner, AEGIS.CvSSourceProduct116.inner, AEGIS.CvSSourceProduct117.inner, AEGIS.CvSSourceProduct118.inner, AEGIS.CvSSourceProduct119.inner, AEGIS.CvSSourceProduct120.inner, AEGIS.CvSSourceProduct121.inner, AEGIS.CvSSourceProduct122.inner, AEGIS.CvSSourceProduct123.inner, AEGIS.CvSSourceProduct124.inner, AEGIS.CvSSourceProduct125.inner, AEGIS.CvSSourceProduct126.inner, AEGIS.CvSSourceProduct127.inner, AEGIS.CvSSourceProduct128.inner, AEGIS.CvSSourceProduct129.inner, AEGIS.CvSSourceProduct130.inner, AEGIS.CvSSourceProduct131.inner, AEGIS.CvSSourceProduct132.inner, AEGIS.CvSSourceProduct133.inner, AEGIS.CvSSourceProduct134.inner, AEGIS.CvSSourceProduct135.inner, AEGIS.CvSSourceProduct136.inner, AEGIS.CvSSourceProduct137.inner, AEGIS.CvSSourceProduct138.inner]
def Y (r : Fin 301) (i : Fin 139) : Iv := (ys.getD i.val []).getD r.val ⟨0, 0⟩
def inner (k : ℕ) (i : Fin 139) : Iv := (inners.getD i.val []).getD k ⟨0, 0⟩

theorem x_transpose (k : Fin 141) (i : Fin 139) :
    (xRow k).values.getD i.val ⟨0, 0⟩ = (inputColumn i).x.values.getD k.val ⟨0, 0⟩ := by
  fin_cases k
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows0.transpose0 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows0.transpose1 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows0.transpose2 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows0.transpose3 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows0.transpose4 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows0.transpose5 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows0.transpose6 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows0.transpose7 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows0.transpose8 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows0.transpose9 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows1.transpose10 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows1.transpose11 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows1.transpose12 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows1.transpose13 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows1.transpose14 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows1.transpose15 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows1.transpose16 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows1.transpose17 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows1.transpose18 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows1.transpose19 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows2.transpose20 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows2.transpose21 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows2.transpose22 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows2.transpose23 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows2.transpose24 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows2.transpose25 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows2.transpose26 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows2.transpose27 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows2.transpose28 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows2.transpose29 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows3.transpose30 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows3.transpose31 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows3.transpose32 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows3.transpose33 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows3.transpose34 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows3.transpose35 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows3.transpose36 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows3.transpose37 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows3.transpose38 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows3.transpose39 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows4.transpose40 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows4.transpose41 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows4.transpose42 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows4.transpose43 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows4.transpose44 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows4.transpose45 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows4.transpose46 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows4.transpose47 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows4.transpose48 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows4.transpose49 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows5.transpose50 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows5.transpose51 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows5.transpose52 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows5.transpose53 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows5.transpose54 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows5.transpose55 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows5.transpose56 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows5.transpose57 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows5.transpose58 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows5.transpose59 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows6.transpose60 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows6.transpose61 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows6.transpose62 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows6.transpose63 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows6.transpose64 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows6.transpose65 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows6.transpose66 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows6.transpose67 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows6.transpose68 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows6.transpose69 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows7.transpose70 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows7.transpose71 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows7.transpose72 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows7.transpose73 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows7.transpose74 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows7.transpose75 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows7.transpose76 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows7.transpose77 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows7.transpose78 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows7.transpose79 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows8.transpose80 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows8.transpose81 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows8.transpose82 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows8.transpose83 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows8.transpose84 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows8.transpose85 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows8.transpose86 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows8.transpose87 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows8.transpose88 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows8.transpose89 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows9.transpose90 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows9.transpose91 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows9.transpose92 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows9.transpose93 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows9.transpose94 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows9.transpose95 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows9.transpose96 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows9.transpose97 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows9.transpose98 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows9.transpose99 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows10.transpose100 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows10.transpose101 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows10.transpose102 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows10.transpose103 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows10.transpose104 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows10.transpose105 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows10.transpose106 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows10.transpose107 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows10.transpose108 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows10.transpose109 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows11.transpose110 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows11.transpose111 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows11.transpose112 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows11.transpose113 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows11.transpose114 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows11.transpose115 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows11.transpose116 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows11.transpose117 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows11.transpose118 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows11.transpose119 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows12.transpose120 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows12.transpose121 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows12.transpose122 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows12.transpose123 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows12.transpose124 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows12.transpose125 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows12.transpose126 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows12.transpose127 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows12.transpose128 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows12.transpose129 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows13.transpose130 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows13.transpose131 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows13.transpose132 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows13.transpose133 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows13.transpose134 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows13.transpose135 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows13.transpose136 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows13.transpose137 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows13.transpose138 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows13.transpose139 i.val (List.mem_range.mpr i.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp AEGIS.CvSSourceXRows14.transpose140 i.val (List.mem_range.mpr i.isLt))
theorem lambda_point (j i : Fin 139) : (lambdaBox j i).lo = (lambdaBox j i).hi := by
  fin_cases i
  · exact point_entry AEGIS.CvSSourceLambdaRows0.row0 AEGIS.CvSSourceLambdaRows0.point0 j
  · exact point_entry AEGIS.CvSSourceLambdaRows0.row1 AEGIS.CvSSourceLambdaRows0.point1 j
  · exact point_entry AEGIS.CvSSourceLambdaRows0.row2 AEGIS.CvSSourceLambdaRows0.point2 j
  · exact point_entry AEGIS.CvSSourceLambdaRows0.row3 AEGIS.CvSSourceLambdaRows0.point3 j
  · exact point_entry AEGIS.CvSSourceLambdaRows0.row4 AEGIS.CvSSourceLambdaRows0.point4 j
  · exact point_entry AEGIS.CvSSourceLambdaRows0.row5 AEGIS.CvSSourceLambdaRows0.point5 j
  · exact point_entry AEGIS.CvSSourceLambdaRows0.row6 AEGIS.CvSSourceLambdaRows0.point6 j
  · exact point_entry AEGIS.CvSSourceLambdaRows0.row7 AEGIS.CvSSourceLambdaRows0.point7 j
  · exact point_entry AEGIS.CvSSourceLambdaRows0.row8 AEGIS.CvSSourceLambdaRows0.point8 j
  · exact point_entry AEGIS.CvSSourceLambdaRows0.row9 AEGIS.CvSSourceLambdaRows0.point9 j
  · exact point_entry AEGIS.CvSSourceLambdaRows1.row10 AEGIS.CvSSourceLambdaRows1.point10 j
  · exact point_entry AEGIS.CvSSourceLambdaRows1.row11 AEGIS.CvSSourceLambdaRows1.point11 j
  · exact point_entry AEGIS.CvSSourceLambdaRows1.row12 AEGIS.CvSSourceLambdaRows1.point12 j
  · exact point_entry AEGIS.CvSSourceLambdaRows1.row13 AEGIS.CvSSourceLambdaRows1.point13 j
  · exact point_entry AEGIS.CvSSourceLambdaRows1.row14 AEGIS.CvSSourceLambdaRows1.point14 j
  · exact point_entry AEGIS.CvSSourceLambdaRows1.row15 AEGIS.CvSSourceLambdaRows1.point15 j
  · exact point_entry AEGIS.CvSSourceLambdaRows1.row16 AEGIS.CvSSourceLambdaRows1.point16 j
  · exact point_entry AEGIS.CvSSourceLambdaRows1.row17 AEGIS.CvSSourceLambdaRows1.point17 j
  · exact point_entry AEGIS.CvSSourceLambdaRows1.row18 AEGIS.CvSSourceLambdaRows1.point18 j
  · exact point_entry AEGIS.CvSSourceLambdaRows1.row19 AEGIS.CvSSourceLambdaRows1.point19 j
  · exact point_entry AEGIS.CvSSourceLambdaRows2.row20 AEGIS.CvSSourceLambdaRows2.point20 j
  · exact point_entry AEGIS.CvSSourceLambdaRows2.row21 AEGIS.CvSSourceLambdaRows2.point21 j
  · exact point_entry AEGIS.CvSSourceLambdaRows2.row22 AEGIS.CvSSourceLambdaRows2.point22 j
  · exact point_entry AEGIS.CvSSourceLambdaRows2.row23 AEGIS.CvSSourceLambdaRows2.point23 j
  · exact point_entry AEGIS.CvSSourceLambdaRows2.row24 AEGIS.CvSSourceLambdaRows2.point24 j
  · exact point_entry AEGIS.CvSSourceLambdaRows2.row25 AEGIS.CvSSourceLambdaRows2.point25 j
  · exact point_entry AEGIS.CvSSourceLambdaRows2.row26 AEGIS.CvSSourceLambdaRows2.point26 j
  · exact point_entry AEGIS.CvSSourceLambdaRows2.row27 AEGIS.CvSSourceLambdaRows2.point27 j
  · exact point_entry AEGIS.CvSSourceLambdaRows2.row28 AEGIS.CvSSourceLambdaRows2.point28 j
  · exact point_entry AEGIS.CvSSourceLambdaRows2.row29 AEGIS.CvSSourceLambdaRows2.point29 j
  · exact point_entry AEGIS.CvSSourceLambdaRows3.row30 AEGIS.CvSSourceLambdaRows3.point30 j
  · exact point_entry AEGIS.CvSSourceLambdaRows3.row31 AEGIS.CvSSourceLambdaRows3.point31 j
  · exact point_entry AEGIS.CvSSourceLambdaRows3.row32 AEGIS.CvSSourceLambdaRows3.point32 j
  · exact point_entry AEGIS.CvSSourceLambdaRows3.row33 AEGIS.CvSSourceLambdaRows3.point33 j
  · exact point_entry AEGIS.CvSSourceLambdaRows3.row34 AEGIS.CvSSourceLambdaRows3.point34 j
  · exact point_entry AEGIS.CvSSourceLambdaRows3.row35 AEGIS.CvSSourceLambdaRows3.point35 j
  · exact point_entry AEGIS.CvSSourceLambdaRows3.row36 AEGIS.CvSSourceLambdaRows3.point36 j
  · exact point_entry AEGIS.CvSSourceLambdaRows3.row37 AEGIS.CvSSourceLambdaRows3.point37 j
  · exact point_entry AEGIS.CvSSourceLambdaRows3.row38 AEGIS.CvSSourceLambdaRows3.point38 j
  · exact point_entry AEGIS.CvSSourceLambdaRows3.row39 AEGIS.CvSSourceLambdaRows3.point39 j
  · exact point_entry AEGIS.CvSSourceLambdaRows4.row40 AEGIS.CvSSourceLambdaRows4.point40 j
  · exact point_entry AEGIS.CvSSourceLambdaRows4.row41 AEGIS.CvSSourceLambdaRows4.point41 j
  · exact point_entry AEGIS.CvSSourceLambdaRows4.row42 AEGIS.CvSSourceLambdaRows4.point42 j
  · exact point_entry AEGIS.CvSSourceLambdaRows4.row43 AEGIS.CvSSourceLambdaRows4.point43 j
  · exact point_entry AEGIS.CvSSourceLambdaRows4.row44 AEGIS.CvSSourceLambdaRows4.point44 j
  · exact point_entry AEGIS.CvSSourceLambdaRows4.row45 AEGIS.CvSSourceLambdaRows4.point45 j
  · exact point_entry AEGIS.CvSSourceLambdaRows4.row46 AEGIS.CvSSourceLambdaRows4.point46 j
  · exact point_entry AEGIS.CvSSourceLambdaRows4.row47 AEGIS.CvSSourceLambdaRows4.point47 j
  · exact point_entry AEGIS.CvSSourceLambdaRows4.row48 AEGIS.CvSSourceLambdaRows4.point48 j
  · exact point_entry AEGIS.CvSSourceLambdaRows4.row49 AEGIS.CvSSourceLambdaRows4.point49 j
  · exact point_entry AEGIS.CvSSourceLambdaRows5.row50 AEGIS.CvSSourceLambdaRows5.point50 j
  · exact point_entry AEGIS.CvSSourceLambdaRows5.row51 AEGIS.CvSSourceLambdaRows5.point51 j
  · exact point_entry AEGIS.CvSSourceLambdaRows5.row52 AEGIS.CvSSourceLambdaRows5.point52 j
  · exact point_entry AEGIS.CvSSourceLambdaRows5.row53 AEGIS.CvSSourceLambdaRows5.point53 j
  · exact point_entry AEGIS.CvSSourceLambdaRows5.row54 AEGIS.CvSSourceLambdaRows5.point54 j
  · exact point_entry AEGIS.CvSSourceLambdaRows5.row55 AEGIS.CvSSourceLambdaRows5.point55 j
  · exact point_entry AEGIS.CvSSourceLambdaRows5.row56 AEGIS.CvSSourceLambdaRows5.point56 j
  · exact point_entry AEGIS.CvSSourceLambdaRows5.row57 AEGIS.CvSSourceLambdaRows5.point57 j
  · exact point_entry AEGIS.CvSSourceLambdaRows5.row58 AEGIS.CvSSourceLambdaRows5.point58 j
  · exact point_entry AEGIS.CvSSourceLambdaRows5.row59 AEGIS.CvSSourceLambdaRows5.point59 j
  · exact point_entry AEGIS.CvSSourceLambdaRows6.row60 AEGIS.CvSSourceLambdaRows6.point60 j
  · exact point_entry AEGIS.CvSSourceLambdaRows6.row61 AEGIS.CvSSourceLambdaRows6.point61 j
  · exact point_entry AEGIS.CvSSourceLambdaRows6.row62 AEGIS.CvSSourceLambdaRows6.point62 j
  · exact point_entry AEGIS.CvSSourceLambdaRows6.row63 AEGIS.CvSSourceLambdaRows6.point63 j
  · exact point_entry AEGIS.CvSSourceLambdaRows6.row64 AEGIS.CvSSourceLambdaRows6.point64 j
  · exact point_entry AEGIS.CvSSourceLambdaRows6.row65 AEGIS.CvSSourceLambdaRows6.point65 j
  · exact point_entry AEGIS.CvSSourceLambdaRows6.row66 AEGIS.CvSSourceLambdaRows6.point66 j
  · exact point_entry AEGIS.CvSSourceLambdaRows6.row67 AEGIS.CvSSourceLambdaRows6.point67 j
  · exact point_entry AEGIS.CvSSourceLambdaRows6.row68 AEGIS.CvSSourceLambdaRows6.point68 j
  · exact point_entry AEGIS.CvSSourceLambdaRows6.row69 AEGIS.CvSSourceLambdaRows6.point69 j
  · exact point_entry AEGIS.CvSSourceLambdaRows7.row70 AEGIS.CvSSourceLambdaRows7.point70 j
  · exact point_entry AEGIS.CvSSourceLambdaRows7.row71 AEGIS.CvSSourceLambdaRows7.point71 j
  · exact point_entry AEGIS.CvSSourceLambdaRows7.row72 AEGIS.CvSSourceLambdaRows7.point72 j
  · exact point_entry AEGIS.CvSSourceLambdaRows7.row73 AEGIS.CvSSourceLambdaRows7.point73 j
  · exact point_entry AEGIS.CvSSourceLambdaRows7.row74 AEGIS.CvSSourceLambdaRows7.point74 j
  · exact point_entry AEGIS.CvSSourceLambdaRows7.row75 AEGIS.CvSSourceLambdaRows7.point75 j
  · exact point_entry AEGIS.CvSSourceLambdaRows7.row76 AEGIS.CvSSourceLambdaRows7.point76 j
  · exact point_entry AEGIS.CvSSourceLambdaRows7.row77 AEGIS.CvSSourceLambdaRows7.point77 j
  · exact point_entry AEGIS.CvSSourceLambdaRows7.row78 AEGIS.CvSSourceLambdaRows7.point78 j
  · exact point_entry AEGIS.CvSSourceLambdaRows7.row79 AEGIS.CvSSourceLambdaRows7.point79 j
  · exact point_entry AEGIS.CvSSourceLambdaRows8.row80 AEGIS.CvSSourceLambdaRows8.point80 j
  · exact point_entry AEGIS.CvSSourceLambdaRows8.row81 AEGIS.CvSSourceLambdaRows8.point81 j
  · exact point_entry AEGIS.CvSSourceLambdaRows8.row82 AEGIS.CvSSourceLambdaRows8.point82 j
  · exact point_entry AEGIS.CvSSourceLambdaRows8.row83 AEGIS.CvSSourceLambdaRows8.point83 j
  · exact point_entry AEGIS.CvSSourceLambdaRows8.row84 AEGIS.CvSSourceLambdaRows8.point84 j
  · exact point_entry AEGIS.CvSSourceLambdaRows8.row85 AEGIS.CvSSourceLambdaRows8.point85 j
  · exact point_entry AEGIS.CvSSourceLambdaRows8.row86 AEGIS.CvSSourceLambdaRows8.point86 j
  · exact point_entry AEGIS.CvSSourceLambdaRows8.row87 AEGIS.CvSSourceLambdaRows8.point87 j
  · exact point_entry AEGIS.CvSSourceLambdaRows8.row88 AEGIS.CvSSourceLambdaRows8.point88 j
  · exact point_entry AEGIS.CvSSourceLambdaRows8.row89 AEGIS.CvSSourceLambdaRows8.point89 j
  · exact point_entry AEGIS.CvSSourceLambdaRows9.row90 AEGIS.CvSSourceLambdaRows9.point90 j
  · exact point_entry AEGIS.CvSSourceLambdaRows9.row91 AEGIS.CvSSourceLambdaRows9.point91 j
  · exact point_entry AEGIS.CvSSourceLambdaRows9.row92 AEGIS.CvSSourceLambdaRows9.point92 j
  · exact point_entry AEGIS.CvSSourceLambdaRows9.row93 AEGIS.CvSSourceLambdaRows9.point93 j
  · exact point_entry AEGIS.CvSSourceLambdaRows9.row94 AEGIS.CvSSourceLambdaRows9.point94 j
  · exact point_entry AEGIS.CvSSourceLambdaRows9.row95 AEGIS.CvSSourceLambdaRows9.point95 j
  · exact point_entry AEGIS.CvSSourceLambdaRows9.row96 AEGIS.CvSSourceLambdaRows9.point96 j
  · exact point_entry AEGIS.CvSSourceLambdaRows9.row97 AEGIS.CvSSourceLambdaRows9.point97 j
  · exact point_entry AEGIS.CvSSourceLambdaRows9.row98 AEGIS.CvSSourceLambdaRows9.point98 j
  · exact point_entry AEGIS.CvSSourceLambdaRows9.row99 AEGIS.CvSSourceLambdaRows9.point99 j
  · exact point_entry AEGIS.CvSSourceLambdaRows10.row100 AEGIS.CvSSourceLambdaRows10.point100 j
  · exact point_entry AEGIS.CvSSourceLambdaRows10.row101 AEGIS.CvSSourceLambdaRows10.point101 j
  · exact point_entry AEGIS.CvSSourceLambdaRows10.row102 AEGIS.CvSSourceLambdaRows10.point102 j
  · exact point_entry AEGIS.CvSSourceLambdaRows10.row103 AEGIS.CvSSourceLambdaRows10.point103 j
  · exact point_entry AEGIS.CvSSourceLambdaRows10.row104 AEGIS.CvSSourceLambdaRows10.point104 j
  · exact point_entry AEGIS.CvSSourceLambdaRows10.row105 AEGIS.CvSSourceLambdaRows10.point105 j
  · exact point_entry AEGIS.CvSSourceLambdaRows10.row106 AEGIS.CvSSourceLambdaRows10.point106 j
  · exact point_entry AEGIS.CvSSourceLambdaRows10.row107 AEGIS.CvSSourceLambdaRows10.point107 j
  · exact point_entry AEGIS.CvSSourceLambdaRows10.row108 AEGIS.CvSSourceLambdaRows10.point108 j
  · exact point_entry AEGIS.CvSSourceLambdaRows10.row109 AEGIS.CvSSourceLambdaRows10.point109 j
  · exact point_entry AEGIS.CvSSourceLambdaRows11.row110 AEGIS.CvSSourceLambdaRows11.point110 j
  · exact point_entry AEGIS.CvSSourceLambdaRows11.row111 AEGIS.CvSSourceLambdaRows11.point111 j
  · exact point_entry AEGIS.CvSSourceLambdaRows11.row112 AEGIS.CvSSourceLambdaRows11.point112 j
  · exact point_entry AEGIS.CvSSourceLambdaRows11.row113 AEGIS.CvSSourceLambdaRows11.point113 j
  · exact point_entry AEGIS.CvSSourceLambdaRows11.row114 AEGIS.CvSSourceLambdaRows11.point114 j
  · exact point_entry AEGIS.CvSSourceLambdaRows11.row115 AEGIS.CvSSourceLambdaRows11.point115 j
  · exact point_entry AEGIS.CvSSourceLambdaRows11.row116 AEGIS.CvSSourceLambdaRows11.point116 j
  · exact point_entry AEGIS.CvSSourceLambdaRows11.row117 AEGIS.CvSSourceLambdaRows11.point117 j
  · exact point_entry AEGIS.CvSSourceLambdaRows11.row118 AEGIS.CvSSourceLambdaRows11.point118 j
  · exact point_entry AEGIS.CvSSourceLambdaRows11.row119 AEGIS.CvSSourceLambdaRows11.point119 j
  · exact point_entry AEGIS.CvSSourceLambdaRows12.row120 AEGIS.CvSSourceLambdaRows12.point120 j
  · exact point_entry AEGIS.CvSSourceLambdaRows12.row121 AEGIS.CvSSourceLambdaRows12.point121 j
  · exact point_entry AEGIS.CvSSourceLambdaRows12.row122 AEGIS.CvSSourceLambdaRows12.point122 j
  · exact point_entry AEGIS.CvSSourceLambdaRows12.row123 AEGIS.CvSSourceLambdaRows12.point123 j
  · exact point_entry AEGIS.CvSSourceLambdaRows12.row124 AEGIS.CvSSourceLambdaRows12.point124 j
  · exact point_entry AEGIS.CvSSourceLambdaRows12.row125 AEGIS.CvSSourceLambdaRows12.point125 j
  · exact point_entry AEGIS.CvSSourceLambdaRows12.row126 AEGIS.CvSSourceLambdaRows12.point126 j
  · exact point_entry AEGIS.CvSSourceLambdaRows12.row127 AEGIS.CvSSourceLambdaRows12.point127 j
  · exact point_entry AEGIS.CvSSourceLambdaRows12.row128 AEGIS.CvSSourceLambdaRows12.point128 j
  · exact point_entry AEGIS.CvSSourceLambdaRows12.row129 AEGIS.CvSSourceLambdaRows12.point129 j
  · exact point_entry AEGIS.CvSSourceLambdaRows13.row130 AEGIS.CvSSourceLambdaRows13.point130 j
  · exact point_entry AEGIS.CvSSourceLambdaRows13.row131 AEGIS.CvSSourceLambdaRows13.point131 j
  · exact point_entry AEGIS.CvSSourceLambdaRows13.row132 AEGIS.CvSSourceLambdaRows13.point132 j
  · exact point_entry AEGIS.CvSSourceLambdaRows13.row133 AEGIS.CvSSourceLambdaRows13.point133 j
  · exact point_entry AEGIS.CvSSourceLambdaRows13.row134 AEGIS.CvSSourceLambdaRows13.point134 j
  · exact point_entry AEGIS.CvSSourceLambdaRows13.row135 AEGIS.CvSSourceLambdaRows13.point135 j
  · exact point_entry AEGIS.CvSSourceLambdaRows13.row136 AEGIS.CvSSourceLambdaRows13.point136 j
  · exact point_entry AEGIS.CvSSourceLambdaRows13.row137 AEGIS.CvSSourceLambdaRows13.point137 j
  · exact point_entry AEGIS.CvSSourceLambdaRows13.row138 AEGIS.CvSSourceLambdaRows13.point138 j
theorem lambda_mem (j i : Fin 139) : (lambdaBox j i).Mem 96 (lambdaReal j i) :=
  point_mem 96 _ (lambda_point j i)

theorem Y_cached (i : Fin 139) : AEGIS.CvSSourceECacheV1.rows.map
    (fun row => evalDot row (inputColumn i).x) = ys.getD i.val [] := by
  fin_cases i
  · exact AEGIS.CvSSourceProduct0.Y_checked
  · exact AEGIS.CvSSourceProduct1.Y_checked
  · exact AEGIS.CvSSourceProduct2.Y_checked
  · exact AEGIS.CvSSourceProduct3.Y_checked
  · exact AEGIS.CvSSourceProduct4.Y_checked
  · exact AEGIS.CvSSourceProduct5.Y_checked
  · exact AEGIS.CvSSourceProduct6.Y_checked
  · exact AEGIS.CvSSourceProduct7.Y_checked
  · exact AEGIS.CvSSourceProduct8.Y_checked
  · exact AEGIS.CvSSourceProduct9.Y_checked
  · exact AEGIS.CvSSourceProduct10.Y_checked
  · exact AEGIS.CvSSourceProduct11.Y_checked
  · exact AEGIS.CvSSourceProduct12.Y_checked
  · exact AEGIS.CvSSourceProduct13.Y_checked
  · exact AEGIS.CvSSourceProduct14.Y_checked
  · exact AEGIS.CvSSourceProduct15.Y_checked
  · exact AEGIS.CvSSourceProduct16.Y_checked
  · exact AEGIS.CvSSourceProduct17.Y_checked
  · exact AEGIS.CvSSourceProduct18.Y_checked
  · exact AEGIS.CvSSourceProduct19.Y_checked
  · exact AEGIS.CvSSourceProduct20.Y_checked
  · exact AEGIS.CvSSourceProduct21.Y_checked
  · exact AEGIS.CvSSourceProduct22.Y_checked
  · exact AEGIS.CvSSourceProduct23.Y_checked
  · exact AEGIS.CvSSourceProduct24.Y_checked
  · exact AEGIS.CvSSourceProduct25.Y_checked
  · exact AEGIS.CvSSourceProduct26.Y_checked
  · exact AEGIS.CvSSourceProduct27.Y_checked
  · exact AEGIS.CvSSourceProduct28.Y_checked
  · exact AEGIS.CvSSourceProduct29.Y_checked
  · exact AEGIS.CvSSourceProduct30.Y_checked
  · exact AEGIS.CvSSourceProduct31.Y_checked
  · exact AEGIS.CvSSourceProduct32.Y_checked
  · exact AEGIS.CvSSourceProduct33.Y_checked
  · exact AEGIS.CvSSourceProduct34.Y_checked
  · exact AEGIS.CvSSourceProduct35.Y_checked
  · exact AEGIS.CvSSourceProduct36.Y_checked
  · exact AEGIS.CvSSourceProduct37.Y_checked
  · exact AEGIS.CvSSourceProduct38.Y_checked
  · exact AEGIS.CvSSourceProduct39.Y_checked
  · exact AEGIS.CvSSourceProduct40.Y_checked
  · exact AEGIS.CvSSourceProduct41.Y_checked
  · exact AEGIS.CvSSourceProduct42.Y_checked
  · exact AEGIS.CvSSourceProduct43.Y_checked
  · exact AEGIS.CvSSourceProduct44.Y_checked
  · exact AEGIS.CvSSourceProduct45.Y_checked
  · exact AEGIS.CvSSourceProduct46.Y_checked
  · exact AEGIS.CvSSourceProduct47.Y_checked
  · exact AEGIS.CvSSourceProduct48.Y_checked
  · exact AEGIS.CvSSourceProduct49.Y_checked
  · exact AEGIS.CvSSourceProduct50.Y_checked
  · exact AEGIS.CvSSourceProduct51.Y_checked
  · exact AEGIS.CvSSourceProduct52.Y_checked
  · exact AEGIS.CvSSourceProduct53.Y_checked
  · exact AEGIS.CvSSourceProduct54.Y_checked
  · exact AEGIS.CvSSourceProduct55.Y_checked
  · exact AEGIS.CvSSourceProduct56.Y_checked
  · exact AEGIS.CvSSourceProduct57.Y_checked
  · exact AEGIS.CvSSourceProduct58.Y_checked
  · exact AEGIS.CvSSourceProduct59.Y_checked
  · exact AEGIS.CvSSourceProduct60.Y_checked
  · exact AEGIS.CvSSourceProduct61.Y_checked
  · exact AEGIS.CvSSourceProduct62.Y_checked
  · exact AEGIS.CvSSourceProduct63.Y_checked
  · exact AEGIS.CvSSourceProduct64.Y_checked
  · exact AEGIS.CvSSourceProduct65.Y_checked
  · exact AEGIS.CvSSourceProduct66.Y_checked
  · exact AEGIS.CvSSourceProduct67.Y_checked
  · exact AEGIS.CvSSourceProduct68.Y_checked
  · exact AEGIS.CvSSourceProduct69.Y_checked
  · exact AEGIS.CvSSourceProduct70.Y_checked
  · exact AEGIS.CvSSourceProduct71.Y_checked
  · exact AEGIS.CvSSourceProduct72.Y_checked
  · exact AEGIS.CvSSourceProduct73.Y_checked
  · exact AEGIS.CvSSourceProduct74.Y_checked
  · exact AEGIS.CvSSourceProduct75.Y_checked
  · exact AEGIS.CvSSourceProduct76.Y_checked
  · exact AEGIS.CvSSourceProduct77.Y_checked
  · exact AEGIS.CvSSourceProduct78.Y_checked
  · exact AEGIS.CvSSourceProduct79.Y_checked
  · exact AEGIS.CvSSourceProduct80.Y_checked
  · exact AEGIS.CvSSourceProduct81.Y_checked
  · exact AEGIS.CvSSourceProduct82.Y_checked
  · exact AEGIS.CvSSourceProduct83.Y_checked
  · exact AEGIS.CvSSourceProduct84.Y_checked
  · exact AEGIS.CvSSourceProduct85.Y_checked
  · exact AEGIS.CvSSourceProduct86.Y_checked
  · exact AEGIS.CvSSourceProduct87.Y_checked
  · exact AEGIS.CvSSourceProduct88.Y_checked
  · exact AEGIS.CvSSourceProduct89.Y_checked
  · exact AEGIS.CvSSourceProduct90.Y_checked
  · exact AEGIS.CvSSourceProduct91.Y_checked
  · exact AEGIS.CvSSourceProduct92.Y_checked
  · exact AEGIS.CvSSourceProduct93.Y_checked
  · exact AEGIS.CvSSourceProduct94.Y_checked
  · exact AEGIS.CvSSourceProduct95.Y_checked
  · exact AEGIS.CvSSourceProduct96.Y_checked
  · exact AEGIS.CvSSourceProduct97.Y_checked
  · exact AEGIS.CvSSourceProduct98.Y_checked
  · exact AEGIS.CvSSourceProduct99.Y_checked
  · exact AEGIS.CvSSourceProduct100.Y_checked
  · exact AEGIS.CvSSourceProduct101.Y_checked
  · exact AEGIS.CvSSourceProduct102.Y_checked
  · exact AEGIS.CvSSourceProduct103.Y_checked
  · exact AEGIS.CvSSourceProduct104.Y_checked
  · exact AEGIS.CvSSourceProduct105.Y_checked
  · exact AEGIS.CvSSourceProduct106.Y_checked
  · exact AEGIS.CvSSourceProduct107.Y_checked
  · exact AEGIS.CvSSourceProduct108.Y_checked
  · exact AEGIS.CvSSourceProduct109.Y_checked
  · exact AEGIS.CvSSourceProduct110.Y_checked
  · exact AEGIS.CvSSourceProduct111.Y_checked
  · exact AEGIS.CvSSourceProduct112.Y_checked
  · exact AEGIS.CvSSourceProduct113.Y_checked
  · exact AEGIS.CvSSourceProduct114.Y_checked
  · exact AEGIS.CvSSourceProduct115.Y_checked
  · exact AEGIS.CvSSourceProduct116.Y_checked
  · exact AEGIS.CvSSourceProduct117.Y_checked
  · exact AEGIS.CvSSourceProduct118.Y_checked
  · exact AEGIS.CvSSourceProduct119.Y_checked
  · exact AEGIS.CvSSourceProduct120.Y_checked
  · exact AEGIS.CvSSourceProduct121.Y_checked
  · exact AEGIS.CvSSourceProduct122.Y_checked
  · exact AEGIS.CvSSourceProduct123.Y_checked
  · exact AEGIS.CvSSourceProduct124.Y_checked
  · exact AEGIS.CvSSourceProduct125.Y_checked
  · exact AEGIS.CvSSourceProduct126.Y_checked
  · exact AEGIS.CvSSourceProduct127.Y_checked
  · exact AEGIS.CvSSourceProduct128.Y_checked
  · exact AEGIS.CvSSourceProduct129.Y_checked
  · exact AEGIS.CvSSourceProduct130.Y_checked
  · exact AEGIS.CvSSourceProduct131.Y_checked
  · exact AEGIS.CvSSourceProduct132.Y_checked
  · exact AEGIS.CvSSourceProduct133.Y_checked
  · exact AEGIS.CvSSourceProduct134.Y_checked
  · exact AEGIS.CvSSourceProduct135.Y_checked
  · exact AEGIS.CvSSourceProduct136.Y_checked
  · exact AEGIS.CvSSourceProduct137.Y_checked
  · exact AEGIS.CvSSourceProduct138.Y_checked
theorem inner_cached (i : Fin 139) : AEGIS.CvSSourceXCacheV1.rows.map
    (fun row => evalDot row (lambdaColumn i)) = inners.getD i.val [] := by
  fin_cases i
  · exact AEGIS.CvSSourceProduct0.inner_checked
  · exact AEGIS.CvSSourceProduct1.inner_checked
  · exact AEGIS.CvSSourceProduct2.inner_checked
  · exact AEGIS.CvSSourceProduct3.inner_checked
  · exact AEGIS.CvSSourceProduct4.inner_checked
  · exact AEGIS.CvSSourceProduct5.inner_checked
  · exact AEGIS.CvSSourceProduct6.inner_checked
  · exact AEGIS.CvSSourceProduct7.inner_checked
  · exact AEGIS.CvSSourceProduct8.inner_checked
  · exact AEGIS.CvSSourceProduct9.inner_checked
  · exact AEGIS.CvSSourceProduct10.inner_checked
  · exact AEGIS.CvSSourceProduct11.inner_checked
  · exact AEGIS.CvSSourceProduct12.inner_checked
  · exact AEGIS.CvSSourceProduct13.inner_checked
  · exact AEGIS.CvSSourceProduct14.inner_checked
  · exact AEGIS.CvSSourceProduct15.inner_checked
  · exact AEGIS.CvSSourceProduct16.inner_checked
  · exact AEGIS.CvSSourceProduct17.inner_checked
  · exact AEGIS.CvSSourceProduct18.inner_checked
  · exact AEGIS.CvSSourceProduct19.inner_checked
  · exact AEGIS.CvSSourceProduct20.inner_checked
  · exact AEGIS.CvSSourceProduct21.inner_checked
  · exact AEGIS.CvSSourceProduct22.inner_checked
  · exact AEGIS.CvSSourceProduct23.inner_checked
  · exact AEGIS.CvSSourceProduct24.inner_checked
  · exact AEGIS.CvSSourceProduct25.inner_checked
  · exact AEGIS.CvSSourceProduct26.inner_checked
  · exact AEGIS.CvSSourceProduct27.inner_checked
  · exact AEGIS.CvSSourceProduct28.inner_checked
  · exact AEGIS.CvSSourceProduct29.inner_checked
  · exact AEGIS.CvSSourceProduct30.inner_checked
  · exact AEGIS.CvSSourceProduct31.inner_checked
  · exact AEGIS.CvSSourceProduct32.inner_checked
  · exact AEGIS.CvSSourceProduct33.inner_checked
  · exact AEGIS.CvSSourceProduct34.inner_checked
  · exact AEGIS.CvSSourceProduct35.inner_checked
  · exact AEGIS.CvSSourceProduct36.inner_checked
  · exact AEGIS.CvSSourceProduct37.inner_checked
  · exact AEGIS.CvSSourceProduct38.inner_checked
  · exact AEGIS.CvSSourceProduct39.inner_checked
  · exact AEGIS.CvSSourceProduct40.inner_checked
  · exact AEGIS.CvSSourceProduct41.inner_checked
  · exact AEGIS.CvSSourceProduct42.inner_checked
  · exact AEGIS.CvSSourceProduct43.inner_checked
  · exact AEGIS.CvSSourceProduct44.inner_checked
  · exact AEGIS.CvSSourceProduct45.inner_checked
  · exact AEGIS.CvSSourceProduct46.inner_checked
  · exact AEGIS.CvSSourceProduct47.inner_checked
  · exact AEGIS.CvSSourceProduct48.inner_checked
  · exact AEGIS.CvSSourceProduct49.inner_checked
  · exact AEGIS.CvSSourceProduct50.inner_checked
  · exact AEGIS.CvSSourceProduct51.inner_checked
  · exact AEGIS.CvSSourceProduct52.inner_checked
  · exact AEGIS.CvSSourceProduct53.inner_checked
  · exact AEGIS.CvSSourceProduct54.inner_checked
  · exact AEGIS.CvSSourceProduct55.inner_checked
  · exact AEGIS.CvSSourceProduct56.inner_checked
  · exact AEGIS.CvSSourceProduct57.inner_checked
  · exact AEGIS.CvSSourceProduct58.inner_checked
  · exact AEGIS.CvSSourceProduct59.inner_checked
  · exact AEGIS.CvSSourceProduct60.inner_checked
  · exact AEGIS.CvSSourceProduct61.inner_checked
  · exact AEGIS.CvSSourceProduct62.inner_checked
  · exact AEGIS.CvSSourceProduct63.inner_checked
  · exact AEGIS.CvSSourceProduct64.inner_checked
  · exact AEGIS.CvSSourceProduct65.inner_checked
  · exact AEGIS.CvSSourceProduct66.inner_checked
  · exact AEGIS.CvSSourceProduct67.inner_checked
  · exact AEGIS.CvSSourceProduct68.inner_checked
  · exact AEGIS.CvSSourceProduct69.inner_checked
  · exact AEGIS.CvSSourceProduct70.inner_checked
  · exact AEGIS.CvSSourceProduct71.inner_checked
  · exact AEGIS.CvSSourceProduct72.inner_checked
  · exact AEGIS.CvSSourceProduct73.inner_checked
  · exact AEGIS.CvSSourceProduct74.inner_checked
  · exact AEGIS.CvSSourceProduct75.inner_checked
  · exact AEGIS.CvSSourceProduct76.inner_checked
  · exact AEGIS.CvSSourceProduct77.inner_checked
  · exact AEGIS.CvSSourceProduct78.inner_checked
  · exact AEGIS.CvSSourceProduct79.inner_checked
  · exact AEGIS.CvSSourceProduct80.inner_checked
  · exact AEGIS.CvSSourceProduct81.inner_checked
  · exact AEGIS.CvSSourceProduct82.inner_checked
  · exact AEGIS.CvSSourceProduct83.inner_checked
  · exact AEGIS.CvSSourceProduct84.inner_checked
  · exact AEGIS.CvSSourceProduct85.inner_checked
  · exact AEGIS.CvSSourceProduct86.inner_checked
  · exact AEGIS.CvSSourceProduct87.inner_checked
  · exact AEGIS.CvSSourceProduct88.inner_checked
  · exact AEGIS.CvSSourceProduct89.inner_checked
  · exact AEGIS.CvSSourceProduct90.inner_checked
  · exact AEGIS.CvSSourceProduct91.inner_checked
  · exact AEGIS.CvSSourceProduct92.inner_checked
  · exact AEGIS.CvSSourceProduct93.inner_checked
  · exact AEGIS.CvSSourceProduct94.inner_checked
  · exact AEGIS.CvSSourceProduct95.inner_checked
  · exact AEGIS.CvSSourceProduct96.inner_checked
  · exact AEGIS.CvSSourceProduct97.inner_checked
  · exact AEGIS.CvSSourceProduct98.inner_checked
  · exact AEGIS.CvSSourceProduct99.inner_checked
  · exact AEGIS.CvSSourceProduct100.inner_checked
  · exact AEGIS.CvSSourceProduct101.inner_checked
  · exact AEGIS.CvSSourceProduct102.inner_checked
  · exact AEGIS.CvSSourceProduct103.inner_checked
  · exact AEGIS.CvSSourceProduct104.inner_checked
  · exact AEGIS.CvSSourceProduct105.inner_checked
  · exact AEGIS.CvSSourceProduct106.inner_checked
  · exact AEGIS.CvSSourceProduct107.inner_checked
  · exact AEGIS.CvSSourceProduct108.inner_checked
  · exact AEGIS.CvSSourceProduct109.inner_checked
  · exact AEGIS.CvSSourceProduct110.inner_checked
  · exact AEGIS.CvSSourceProduct111.inner_checked
  · exact AEGIS.CvSSourceProduct112.inner_checked
  · exact AEGIS.CvSSourceProduct113.inner_checked
  · exact AEGIS.CvSSourceProduct114.inner_checked
  · exact AEGIS.CvSSourceProduct115.inner_checked
  · exact AEGIS.CvSSourceProduct116.inner_checked
  · exact AEGIS.CvSSourceProduct117.inner_checked
  · exact AEGIS.CvSSourceProduct118.inner_checked
  · exact AEGIS.CvSSourceProduct119.inner_checked
  · exact AEGIS.CvSSourceProduct120.inner_checked
  · exact AEGIS.CvSSourceProduct121.inner_checked
  · exact AEGIS.CvSSourceProduct122.inner_checked
  · exact AEGIS.CvSSourceProduct123.inner_checked
  · exact AEGIS.CvSSourceProduct124.inner_checked
  · exact AEGIS.CvSSourceProduct125.inner_checked
  · exact AEGIS.CvSSourceProduct126.inner_checked
  · exact AEGIS.CvSSourceProduct127.inner_checked
  · exact AEGIS.CvSSourceProduct128.inner_checked
  · exact AEGIS.CvSSourceProduct129.inner_checked
  · exact AEGIS.CvSSourceProduct130.inner_checked
  · exact AEGIS.CvSSourceProduct131.inner_checked
  · exact AEGIS.CvSSourceProduct132.inner_checked
  · exact AEGIS.CvSSourceProduct133.inner_checked
  · exact AEGIS.CvSSourceProduct134.inner_checked
  · exact AEGIS.CvSSourceProduct135.inner_checked
  · exact AEGIS.CvSSourceProduct136.inner_checked
  · exact AEGIS.CvSSourceProduct137.inner_checked
  · exact AEGIS.CvSSourceProduct138.inner_checked
theorem Y_entry (r : Fin 301) (i : Fin 139) : Y r i =
    AEGIS.CvSListIntervalDotV1.listDot 96 (eRow r).values (inputColumn i).x.values :=
  product_entry_eq (by decide) (by decide) AEGIS.CvSSourceECacheV1.rows
    AEGIS.CvSSourceERows0.row0 (inputColumn i).x (ys.getD i.val [])
    AEGIS.CvSSourceECacheV1.length_eq (Y_cached i) r

theorem inner_entry (k : Fin 141) (i : Fin 139) : inner k.val i =
    AEGIS.CvSListIntervalDotV1.listDot 96 (xRow k).values (lambdaColumn i).values :=
  product_entry_eq (by decide) (by decide) AEGIS.CvSSourceXCacheV1.rows
    AEGIS.CvSSourceXRows0.row0 (lambdaColumn i) (inners.getD i.val [])
    AEGIS.CvSSourceXCacheV1.length_eq (inner_cached i) k

theorem Z_entry (r : Fin 301) (i : Fin 139) :
    (inputColumn i).z.values.getD r.val ⟨0, 0⟩ =
      if 80 ≤ r.val ∧ r.val < 221 then (Y r i).add (inner (r.val - 80) i).neg
      else Y r i := by
  fin_cases i
  · exact AEGIS.CvSSourceProduct0.Z_exact r
  · exact AEGIS.CvSSourceProduct1.Z_exact r
  · exact AEGIS.CvSSourceProduct2.Z_exact r
  · exact AEGIS.CvSSourceProduct3.Z_exact r
  · exact AEGIS.CvSSourceProduct4.Z_exact r
  · exact AEGIS.CvSSourceProduct5.Z_exact r
  · exact AEGIS.CvSSourceProduct6.Z_exact r
  · exact AEGIS.CvSSourceProduct7.Z_exact r
  · exact AEGIS.CvSSourceProduct8.Z_exact r
  · exact AEGIS.CvSSourceProduct9.Z_exact r
  · exact AEGIS.CvSSourceProduct10.Z_exact r
  · exact AEGIS.CvSSourceProduct11.Z_exact r
  · exact AEGIS.CvSSourceProduct12.Z_exact r
  · exact AEGIS.CvSSourceProduct13.Z_exact r
  · exact AEGIS.CvSSourceProduct14.Z_exact r
  · exact AEGIS.CvSSourceProduct15.Z_exact r
  · exact AEGIS.CvSSourceProduct16.Z_exact r
  · exact AEGIS.CvSSourceProduct17.Z_exact r
  · exact AEGIS.CvSSourceProduct18.Z_exact r
  · exact AEGIS.CvSSourceProduct19.Z_exact r
  · exact AEGIS.CvSSourceProduct20.Z_exact r
  · exact AEGIS.CvSSourceProduct21.Z_exact r
  · exact AEGIS.CvSSourceProduct22.Z_exact r
  · exact AEGIS.CvSSourceProduct23.Z_exact r
  · exact AEGIS.CvSSourceProduct24.Z_exact r
  · exact AEGIS.CvSSourceProduct25.Z_exact r
  · exact AEGIS.CvSSourceProduct26.Z_exact r
  · exact AEGIS.CvSSourceProduct27.Z_exact r
  · exact AEGIS.CvSSourceProduct28.Z_exact r
  · exact AEGIS.CvSSourceProduct29.Z_exact r
  · exact AEGIS.CvSSourceProduct30.Z_exact r
  · exact AEGIS.CvSSourceProduct31.Z_exact r
  · exact AEGIS.CvSSourceProduct32.Z_exact r
  · exact AEGIS.CvSSourceProduct33.Z_exact r
  · exact AEGIS.CvSSourceProduct34.Z_exact r
  · exact AEGIS.CvSSourceProduct35.Z_exact r
  · exact AEGIS.CvSSourceProduct36.Z_exact r
  · exact AEGIS.CvSSourceProduct37.Z_exact r
  · exact AEGIS.CvSSourceProduct38.Z_exact r
  · exact AEGIS.CvSSourceProduct39.Z_exact r
  · exact AEGIS.CvSSourceProduct40.Z_exact r
  · exact AEGIS.CvSSourceProduct41.Z_exact r
  · exact AEGIS.CvSSourceProduct42.Z_exact r
  · exact AEGIS.CvSSourceProduct43.Z_exact r
  · exact AEGIS.CvSSourceProduct44.Z_exact r
  · exact AEGIS.CvSSourceProduct45.Z_exact r
  · exact AEGIS.CvSSourceProduct46.Z_exact r
  · exact AEGIS.CvSSourceProduct47.Z_exact r
  · exact AEGIS.CvSSourceProduct48.Z_exact r
  · exact AEGIS.CvSSourceProduct49.Z_exact r
  · exact AEGIS.CvSSourceProduct50.Z_exact r
  · exact AEGIS.CvSSourceProduct51.Z_exact r
  · exact AEGIS.CvSSourceProduct52.Z_exact r
  · exact AEGIS.CvSSourceProduct53.Z_exact r
  · exact AEGIS.CvSSourceProduct54.Z_exact r
  · exact AEGIS.CvSSourceProduct55.Z_exact r
  · exact AEGIS.CvSSourceProduct56.Z_exact r
  · exact AEGIS.CvSSourceProduct57.Z_exact r
  · exact AEGIS.CvSSourceProduct58.Z_exact r
  · exact AEGIS.CvSSourceProduct59.Z_exact r
  · exact AEGIS.CvSSourceProduct60.Z_exact r
  · exact AEGIS.CvSSourceProduct61.Z_exact r
  · exact AEGIS.CvSSourceProduct62.Z_exact r
  · exact AEGIS.CvSSourceProduct63.Z_exact r
  · exact AEGIS.CvSSourceProduct64.Z_exact r
  · exact AEGIS.CvSSourceProduct65.Z_exact r
  · exact AEGIS.CvSSourceProduct66.Z_exact r
  · exact AEGIS.CvSSourceProduct67.Z_exact r
  · exact AEGIS.CvSSourceProduct68.Z_exact r
  · exact AEGIS.CvSSourceProduct69.Z_exact r
  · exact AEGIS.CvSSourceProduct70.Z_exact r
  · exact AEGIS.CvSSourceProduct71.Z_exact r
  · exact AEGIS.CvSSourceProduct72.Z_exact r
  · exact AEGIS.CvSSourceProduct73.Z_exact r
  · exact AEGIS.CvSSourceProduct74.Z_exact r
  · exact AEGIS.CvSSourceProduct75.Z_exact r
  · exact AEGIS.CvSSourceProduct76.Z_exact r
  · exact AEGIS.CvSSourceProduct77.Z_exact r
  · exact AEGIS.CvSSourceProduct78.Z_exact r
  · exact AEGIS.CvSSourceProduct79.Z_exact r
  · exact AEGIS.CvSSourceProduct80.Z_exact r
  · exact AEGIS.CvSSourceProduct81.Z_exact r
  · exact AEGIS.CvSSourceProduct82.Z_exact r
  · exact AEGIS.CvSSourceProduct83.Z_exact r
  · exact AEGIS.CvSSourceProduct84.Z_exact r
  · exact AEGIS.CvSSourceProduct85.Z_exact r
  · exact AEGIS.CvSSourceProduct86.Z_exact r
  · exact AEGIS.CvSSourceProduct87.Z_exact r
  · exact AEGIS.CvSSourceProduct88.Z_exact r
  · exact AEGIS.CvSSourceProduct89.Z_exact r
  · exact AEGIS.CvSSourceProduct90.Z_exact r
  · exact AEGIS.CvSSourceProduct91.Z_exact r
  · exact AEGIS.CvSSourceProduct92.Z_exact r
  · exact AEGIS.CvSSourceProduct93.Z_exact r
  · exact AEGIS.CvSSourceProduct94.Z_exact r
  · exact AEGIS.CvSSourceProduct95.Z_exact r
  · exact AEGIS.CvSSourceProduct96.Z_exact r
  · exact AEGIS.CvSSourceProduct97.Z_exact r
  · exact AEGIS.CvSSourceProduct98.Z_exact r
  · exact AEGIS.CvSSourceProduct99.Z_exact r
  · exact AEGIS.CvSSourceProduct100.Z_exact r
  · exact AEGIS.CvSSourceProduct101.Z_exact r
  · exact AEGIS.CvSSourceProduct102.Z_exact r
  · exact AEGIS.CvSSourceProduct103.Z_exact r
  · exact AEGIS.CvSSourceProduct104.Z_exact r
  · exact AEGIS.CvSSourceProduct105.Z_exact r
  · exact AEGIS.CvSSourceProduct106.Z_exact r
  · exact AEGIS.CvSSourceProduct107.Z_exact r
  · exact AEGIS.CvSSourceProduct108.Z_exact r
  · exact AEGIS.CvSSourceProduct109.Z_exact r
  · exact AEGIS.CvSSourceProduct110.Z_exact r
  · exact AEGIS.CvSSourceProduct111.Z_exact r
  · exact AEGIS.CvSSourceProduct112.Z_exact r
  · exact AEGIS.CvSSourceProduct113.Z_exact r
  · exact AEGIS.CvSSourceProduct114.Z_exact r
  · exact AEGIS.CvSSourceProduct115.Z_exact r
  · exact AEGIS.CvSSourceProduct116.Z_exact r
  · exact AEGIS.CvSSourceProduct117.Z_exact r
  · exact AEGIS.CvSSourceProduct118.Z_exact r
  · exact AEGIS.CvSSourceProduct119.Z_exact r
  · exact AEGIS.CvSSourceProduct120.Z_exact r
  · exact AEGIS.CvSSourceProduct121.Z_exact r
  · exact AEGIS.CvSSourceProduct122.Z_exact r
  · exact AEGIS.CvSSourceProduct123.Z_exact r
  · exact AEGIS.CvSSourceProduct124.Z_exact r
  · exact AEGIS.CvSSourceProduct125.Z_exact r
  · exact AEGIS.CvSSourceProduct126.Z_exact r
  · exact AEGIS.CvSSourceProduct127.Z_exact r
  · exact AEGIS.CvSSourceProduct128.Z_exact r
  · exact AEGIS.CvSSourceProduct129.Z_exact r
  · exact AEGIS.CvSSourceProduct130.Z_exact r
  · exact AEGIS.CvSSourceProduct131.Z_exact r
  · exact AEGIS.CvSSourceProduct132.Z_exact r
  · exact AEGIS.CvSSourceProduct133.Z_exact r
  · exact AEGIS.CvSSourceProduct134.Z_exact r
  · exact AEGIS.CvSSourceProduct135.Z_exact r
  · exact AEGIS.CvSSourceProduct136.Z_exact r
  · exact AEGIS.CvSSourceProduct137.Z_exact r
  · exact AEGIS.CvSSourceProduct138.Z_exact r
end AEGIS.CvSSourceProductAllV1
#check @AEGIS.CvSSourceProductAllV1.x_transpose
#print axioms AEGIS.CvSSourceProductAllV1.x_transpose
#check @AEGIS.CvSSourceProductAllV1.lambda_point
#print axioms AEGIS.CvSSourceProductAllV1.lambda_point
#check @AEGIS.CvSSourceProductAllV1.lambda_mem
#print axioms AEGIS.CvSSourceProductAllV1.lambda_mem
#check @AEGIS.CvSSourceProductAllV1.Y_cached
#print axioms AEGIS.CvSSourceProductAllV1.Y_cached
#check @AEGIS.CvSSourceProductAllV1.inner_cached
#print axioms AEGIS.CvSSourceProductAllV1.inner_cached
#check @AEGIS.CvSSourceProductAllV1.Y_entry
#print axioms AEGIS.CvSSourceProductAllV1.Y_entry
#check @AEGIS.CvSSourceProductAllV1.inner_entry
#print axioms AEGIS.CvSSourceProductAllV1.inner_entry
#check @AEGIS.CvSSourceProductAllV1.Z_entry
#print axioms AEGIS.CvSSourceProductAllV1.Z_entry
