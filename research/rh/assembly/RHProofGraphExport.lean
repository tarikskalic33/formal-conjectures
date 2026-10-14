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
import AEGISOverlay.AEGIS_RH_Unconditional
import AEGISOverlay.RHFiniteActualGramJoinV1
import RHCofinalSchurAdapterV1
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

open Lean Elab Command

set_option maxHeartbeats 0

elab "#export_rh_proof_graph" : command => do
  let env ← getEnv
  let roots : List Name := [
    "AEGIS.RHAssemblyV1.narrow_window_schur_family",
    "AEGIS.RHAssemblyV1.narrow_window_schur_norm_family",
    "AEGIS.RHFeshbachWeilClosureV2.riemannHypothesis_of_window_schur_families",
    "AEGIS.RHFiniteActualGramJoinV1.every_packet_actual_finite_gram",
    "AEGIS.RHCofinalSchurAdapterV1.actual_zero_quadratic_nonnegative_of_gram_bounds"].map
      (fun s => (s.splitOn ".").foldl Name.str Name.anonymous)
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := (env.setExporting false).find? n then
      let deps := ci.getUsedConstantsAsSet.toList
      pending := deps ++ pending
      let mod := match env.getModuleIdxFor? n with
        | some i => env.header.modules[i.toNat]!.module.toString
        | none => "RHProofGraphExport"
      let ax := match ci with | .axiomInfo _ => true | _ => false
      let axioms ← collectAxioms n
      rows := rows.push (Json.mkObj [
        ("identifier", toJson n.toString),
        ("module", toJson mod),
        ("type_expr", toJson (toString ci.type)),
        ("direct_dependencies", toJson (deps.map Name.toString)),
        ("is_axiom", toJson ax),
        ("axioms", toJson (axioms.map Name.toString)),
        ("has_body", toJson (ci.value? (allowOpaque := true)).isSome)])
  liftIO <| IO.FS.createDirAll "evidence-cofinal/assembly"
  liftIO <| IO.FS.writeFile "evidence-cofinal/assembly/proof-terms.json"
    (Json.mkObj [("roots",toJson (roots.map Name.toString)),
      ("declarations",Json.arr rows)]).pretty
  logInfo m!"PROOF_TERM_GRAPH_DECLARATIONS {rows.size}"

#export_rh_proof_graph
