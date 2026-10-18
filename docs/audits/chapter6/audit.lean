import BC4lean.CZeroAlgebra
import BC4lean.CZeroHomotopy
import BC4lean.CZeroPullback
import BC4lean.CZeroSeparability
import BC4lean.CocompactPieceMap
import BC4lean.CocompactPieceMapHomotopy
import BC4lean.CocompactPieceRepresentatives
import BC4lean.DirectedAddGroupColimit
import BC4lean.DirectedAddGroupColimitCofinal
import BC4lean.DirectedAddGroupColimitMap
import BC4lean.KasparovSourceHomotopy
import BC4lean.KasparovSourceHomotopyParity
import BC4lean.TopologicalKHomologyColimit
import BC4lean.TopologicalKHomologyDiagram
import BC4lean.TopologicalKHomologyHomotopy
import BC4lean.TopologicalKHomologyMaps
import Lean
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env := (← getEnv).setExporting false
  let modules : Array String := #["BC4lean.CZeroAlgebra", "BC4lean.CZeroHomotopy", "BC4lean.CZeroPullback", "BC4lean.CZeroSeparability", "BC4lean.CocompactPieceMap", "BC4lean.CocompactPieceMapHomotopy", "BC4lean.CocompactPieceRepresentatives", "BC4lean.DirectedAddGroupColimit", "BC4lean.DirectedAddGroupColimitCofinal", "BC4lean.DirectedAddGroupColimitMap", "BC4lean.KasparovSourceHomotopy", "BC4lean.KasparovSourceHomotopyParity", "BC4lean.TopologicalKHomologyColimit", "BC4lean.TopologicalKHomologyDiagram", "BC4lean.TopologicalKHomologyHomotopy", "BC4lean.TopologicalKHomologyMaps"]
  let links : Array String := #["BC4lean.KKTheory.CZero.action", "BC4lean.KKTheory.CZero.action_apply", "BC4lean.KKTheory.CZero.pieceRestriction", "BC4lean.KKTheory.CZero.pieceRestriction_comp", "BC4lean.KKTheory.CZero.pieceRestriction_equivariant", "BC4lean.TopologicalKHomology.cZero_separableSpace", "BC4lean.TopologicalKHomology.cofinalIndexEquiv", "BC4lean.TopologicalKHomology.diagram", "BC4lean.TopologicalKHomology.existsUnique_desc", "BC4lean.TopologicalKHomology.group", "BC4lean.TopologicalKHomology.homotopyEquiv", "BC4lean.TopologicalKHomology.ofPiece_eq_iff", "BC4lean.TopologicalKHomology.pieceGroup", "BC4lean.TopologicalKHomology.pushforward_homotopy", "BC4lean.TopologicalKHomology.spaceGroup", "BC4lean.TopologicalKHomology.toCanonicalModelEquiv", "BC4lean.TopologicalKHomology.topologicalGroup", "BC4lean.TopologicalKHomology.transition", "BC4lean.TopologicalKHomology.transition_refl", "BC4lean.TopologicalKHomology.transition_trans", "BC4lean.TopologicalKHomology.universalComparison_unique", "BC4lean.TopologicalKHomology.universalModelEquiv"]
  let endpoints : Array String := #["BC4lean.TopologicalKHomology.cofinalIndexEquiv", "BC4lean.TopologicalKHomology.diagram", "BC4lean.TopologicalKHomology.existsUnique_desc", "BC4lean.TopologicalKHomology.group", "BC4lean.TopologicalKHomology.homotopyEquiv", "BC4lean.TopologicalKHomology.ofPiece_eq_iff", "BC4lean.TopologicalKHomology.pieceGroup", "BC4lean.TopologicalKHomology.pushforward_homotopy", "BC4lean.TopologicalKHomology.spaceGroup", "BC4lean.TopologicalKHomology.toCanonicalModelEquiv", "BC4lean.TopologicalKHomology.topologicalGroup", "BC4lean.TopologicalKHomology.transition", "BC4lean.TopologicalKHomology.transition_refl", "BC4lean.TopologicalKHomology.transition_trans", "BC4lean.TopologicalKHomology.universalComparison_unique", "BC4lean.TopologicalKHomology.universalModelEquiv"]
  let mut declarations : Array (String × Name) := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let origin := env.header.moduleNames[idx]!.toString
      if modules.contains origin then
        if info matches .axiomInfo _ then
          throwError "New axiom declaration {name} in {origin}"
        declarations := declarations.push (origin, name)
  liftIO <| IO.println "CH6_START|1"
  for (origin, name) in declarations do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom {axiomName} in {name}"
    let axiomText := String.intercalate "," (axioms.toList.map Name.toString)
    liftIO <| IO.println s!"CH6_DECL|{origin}|{name.toString}|{axiomText}"
  for text in (links ++ endpoints).toList.eraseDups do
    let name := text.toName
    unless (env.find? name).isSome do
      throwError "Unknown exact blueprint/endpoint declaration {text}"
    if endpoints.contains text then
      let some idx := env.getModuleIdxFor? name
        | throwError "Missing imported endpoint origin {text}"
      unless modules.contains env.header.moduleNames[idx]!.toString do
        throwError "Required endpoint outside the Chapter 6 declaration scope: {text}"
  for text in links do
    let name := text.toName
    let some idx := env.getModuleIdxFor? name
      | throwError "Missing imported origin for blueprint link {text}"
    let origin := env.header.moduleNames[idx]!.toString
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom {axiomName} in blueprint link {text}"
    let axiomText := String.intercalate "," (axioms.toList.map Name.toString)
    liftIO <| IO.println s!"CH6_LINK|{text}|{origin}|{axiomText}"
  for origin in modules do
    let count := (declarations.filter (·.1 == origin)).size
    liftIO <| IO.println s!"CH6_MODULE|{origin}|{count}"
  liftIO <| IO.println s!"CH6_END|{declarations.size}|{links.size}"
