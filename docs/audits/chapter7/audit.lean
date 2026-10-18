import BC4lean.AlgebraicCrossedProduct
import BC4lean.AlgebraicCrossedRepresentation
import BC4lean.CocompactPieceCutoff
import BC4lean.CutoffAlgebraicProjection
import BC4lean.CutoffCoefficientProjection
import BC4lean.KasparovDescentCompactAction
import BC4lean.KasparovDescentModule
import BC4lean.NonunitalProjectionK0
import BC4lean.ProperCutoffFunction
import BC4lean.ReducedCrossedHilbertModule
import BC4lean.ReducedCrossedNorm
import BC4lean.ReducedCrossedProduct
import BC4lean.ReducedCrossedRegularOperators
import BC4lean.ReducedCrossedScalarHilbert
import BC4lean.ReducedCrossedScalarProduct
import BC4lean.ReducedCutoffProjection
import Lean
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let modules : Array String := #["BC4lean.AlgebraicCrossedProduct", "BC4lean.AlgebraicCrossedRepresentation", "BC4lean.CocompactPieceCutoff", "BC4lean.CutoffAlgebraicProjection", "BC4lean.CutoffCoefficientProjection", "BC4lean.KasparovDescentCompactAction", "BC4lean.KasparovDescentModule", "BC4lean.NonunitalProjectionK0", "BC4lean.ProperCutoffFunction", "BC4lean.ReducedCrossedHilbertModule", "BC4lean.ReducedCrossedNorm", "BC4lean.ReducedCrossedProduct", "BC4lean.ReducedCrossedRegularOperators", "BC4lean.ReducedCrossedScalarHilbert", "BC4lean.ReducedCrossedScalarProduct", "BC4lean.ReducedCutoffProjection"]
  let links : Array String := #["BC4lean.KKTheory.AlgebraicCrossedProduct", "BC4lean.KKTheory.AlgebraicCrossedProduct.coeff_mul", "BC4lean.KKTheory.AlgebraicCrossedProduct.coeff_star", "BC4lean.KKTheory.EquivariantHilbertModule.adjointableAction", "BC4lean.KKTheory.EquivariantHilbertModule.compactOperatorAction", "BC4lean.KKTheory.EquivariantHilbertModule.compactOperatorAction_equivariant", "BC4lean.KKTheory.EquivariantHilbertModule.compactOperatorAction_rankOne", "BC4lean.KKTheory.KasparovDescent.Module", "BC4lean.KKTheory.KasparovDescent.coefficientRepresentation", "BC4lean.KKTheory.KasparovDescent.countablyGenerated", "BC4lean.KKTheory.KasparovDescent.mk_balance", "BC4lean.KKTheory.KasparovDescent.mk_inner", "BC4lean.KKTheory.KasparovDescent.norm_operatorHom_le", "BC4lean.KKTheory.KasparovDescent.operatorHom_adjoint", "BC4lean.KKTheory.KasparovDescent.operatorHom_compact", "BC4lean.KKTheory.KasparovDescent.operatorHom_mk", "BC4lean.KKTheory.ReducedCrossedHilbertModule", "BC4lean.KKTheory.ReducedCrossedProduct", "BC4lean.KKTheory.algebraicCrossedOperatorHom_eq_sum", "BC4lean.KKTheory.algebraicCrossedReducedNorm", "BC4lean.KKTheory.algebraicCrossedReducedNorm_cstar", "BC4lean.KKTheory.algebraicCrossedReducedNorm_eq_zero", "BC4lean.KKTheory.algebraicToReducedCrossed", "BC4lean.KKTheory.algebraicToReducedCrossed_denseRange", "BC4lean.KKTheory.algebraicToReducedCrossed_injective", "BC4lean.KKTheory.coefficientToReducedCrossed", "BC4lean.KKTheory.norm_coefficientToReducedCrossed", "BC4lean.KKTheory.norm_reducedCrossedCoefficient", "BC4lean.KKTheory.reducedCrossedAlgebra_coe_eq_closure_span", "BC4lean.KKTheory.reducedCrossedCoefficient", "BC4lean.KKTheory.reducedCrossedEvaluation_coefficient", "BC4lean.KKTheory.reducedCrossedEvaluation_regular", "BC4lean.KKTheory.reducedCrossedFiniteInner_self_eq_zero_iff", "BC4lean.KKTheory.reducedCrossedMk_denseRange", "BC4lean.KKTheory.reducedCrossedMk_norm_coefficients", "BC4lean.KKTheory.reducedCrossedProduct_nonUnitalCStarAlgebra", "BC4lean.KKTheory.reducedCrossedProduct_separableSpace", "BC4lean.KKTheory.reducedCrossedRegular", "BC4lean.KKTheory.reducedCrossedScalarHilbertEquiv", "BC4lean.KKTheory.reducedCrossedScalarOperatorEquiv_generator", "BC4lean.KKTheory.reducedCrossedScalarProductEquiv", "BC4lean.KKTheory.reducedCrossedScalarProductEquiv_oneCoefficient", "BC4lean.KKTheory.reducedCrossed_covariance", "BC4lean.OperatorKTheory.nonunitalProjectionK0", "BC4lean.OperatorKTheory.nonunitalProjectionK0_eq_of_partialIsometry", "BC4lean.OperatorKTheory.operatorK0Inclusion_nonunitalProjectionK0", "BC4lean.ProperActions.CocompactPiece.exists_cutoffFunction", "BC4lean.ProperActions.CocompactPiece.proper", "BC4lean.ProperActions.Cutoff.CutoffFunction", "BC4lean.ProperActions.Cutoff.algebraicProjection", "BC4lean.ProperActions.Cutoff.algebraicProjection_mul_self", "BC4lean.ProperActions.Cutoff.coeff_mixedAlgebraic", "BC4lean.ProperActions.Cutoff.cutoffK0", "BC4lean.ProperActions.Cutoff.cutoffK0_independent", "BC4lean.ProperActions.Cutoff.exists_cutoffFunction", "BC4lean.ProperActions.Cutoff.finite_mixedCoefficient_support", "BC4lean.ProperActions.Cutoff.mixedAlgebraic", "BC4lean.ProperActions.Cutoff.mixedAlgebraic_partialIsometry", "BC4lean.ProperActions.Cutoff.normalized_tsum", "BC4lean.ProperActions.Cutoff.reducedCutoffProjection", "BC4lean.ProperActions.Cutoff.reducedCutoffProjection_isStarProjection", "BC4lean.ProperActions.Cutoff.reducedCutoffProjection_partialIsometry", "BC4lean.ProperActions.Cutoff.star_algebraicProjection", "BC4lean.ProperActions.CutoffCoefficients.convolution_mixed_of_normalized", "BC4lean.ProperActions.CutoffCoefficients.involution_mixed"]
  let endpoints : Array String := #["BC4lean.KKTheory.AlgebraicCrossedProduct", "BC4lean.KKTheory.AlgebraicCrossedProduct.coeff_mul", "BC4lean.KKTheory.AlgebraicCrossedProduct.coeff_star", "BC4lean.KKTheory.EquivariantHilbertModule.adjointableAction", "BC4lean.KKTheory.EquivariantHilbertModule.compactOperatorAction", "BC4lean.KKTheory.EquivariantHilbertModule.compactOperatorAction_equivariant", "BC4lean.KKTheory.EquivariantHilbertModule.compactOperatorAction_rankOne", "BC4lean.KKTheory.KasparovDescent.Module", "BC4lean.KKTheory.KasparovDescent.coefficientRepresentation", "BC4lean.KKTheory.KasparovDescent.countablyGenerated", "BC4lean.KKTheory.KasparovDescent.mk_balance", "BC4lean.KKTheory.KasparovDescent.mk_inner", "BC4lean.KKTheory.KasparovDescent.norm_operatorHom_le", "BC4lean.KKTheory.KasparovDescent.operatorHom_adjoint", "BC4lean.KKTheory.KasparovDescent.operatorHom_compact", "BC4lean.KKTheory.KasparovDescent.operatorHom_mk", "BC4lean.KKTheory.ReducedCrossedHilbertModule", "BC4lean.KKTheory.ReducedCrossedProduct", "BC4lean.KKTheory.algebraicCrossedOperatorHom_eq_sum", "BC4lean.KKTheory.algebraicCrossedReducedNorm", "BC4lean.KKTheory.algebraicCrossedReducedNorm_cstar", "BC4lean.KKTheory.algebraicCrossedReducedNorm_eq_zero", "BC4lean.KKTheory.algebraicToReducedCrossed", "BC4lean.KKTheory.algebraicToReducedCrossed_denseRange", "BC4lean.KKTheory.algebraicToReducedCrossed_injective", "BC4lean.KKTheory.coefficientToReducedCrossed", "BC4lean.KKTheory.norm_coefficientToReducedCrossed", "BC4lean.KKTheory.norm_reducedCrossedCoefficient", "BC4lean.KKTheory.reducedCrossedAlgebra_coe_eq_closure_span", "BC4lean.KKTheory.reducedCrossedCoefficient", "BC4lean.KKTheory.reducedCrossedEvaluation_coefficient", "BC4lean.KKTheory.reducedCrossedEvaluation_regular", "BC4lean.KKTheory.reducedCrossedFiniteInner_self_eq_zero_iff", "BC4lean.KKTheory.reducedCrossedMk_denseRange", "BC4lean.KKTheory.reducedCrossedMk_norm_coefficients", "BC4lean.KKTheory.reducedCrossedProduct_nonUnitalCStarAlgebra", "BC4lean.KKTheory.reducedCrossedProduct_separableSpace", "BC4lean.KKTheory.reducedCrossedRegular", "BC4lean.KKTheory.reducedCrossedScalarHilbertEquiv", "BC4lean.KKTheory.reducedCrossedScalarOperatorEquiv_generator", "BC4lean.KKTheory.reducedCrossedScalarProductEquiv", "BC4lean.KKTheory.reducedCrossedScalarProductEquiv_oneCoefficient", "BC4lean.KKTheory.reducedCrossed_covariance", "BC4lean.OperatorKTheory.nonunitalProjectionK0", "BC4lean.OperatorKTheory.nonunitalProjectionK0_eq_of_partialIsometry", "BC4lean.OperatorKTheory.operatorK0Inclusion_nonunitalProjectionK0", "BC4lean.ProperActions.CocompactPiece.exists_cutoffFunction", "BC4lean.ProperActions.CocompactPiece.proper", "BC4lean.ProperActions.Cutoff.CutoffFunction", "BC4lean.ProperActions.Cutoff.algebraicProjection", "BC4lean.ProperActions.Cutoff.algebraicProjection_mul_self", "BC4lean.ProperActions.Cutoff.coeff_mixedAlgebraic", "BC4lean.ProperActions.Cutoff.cutoffK0", "BC4lean.ProperActions.Cutoff.cutoffK0_independent", "BC4lean.ProperActions.Cutoff.exists_cutoffFunction", "BC4lean.ProperActions.Cutoff.finite_mixedCoefficient_support", "BC4lean.ProperActions.Cutoff.mixedAlgebraic", "BC4lean.ProperActions.Cutoff.mixedAlgebraic_partialIsometry", "BC4lean.ProperActions.Cutoff.normalized_tsum", "BC4lean.ProperActions.Cutoff.reducedCutoffProjection", "BC4lean.ProperActions.Cutoff.reducedCutoffProjection_isStarProjection", "BC4lean.ProperActions.Cutoff.reducedCutoffProjection_partialIsometry", "BC4lean.ProperActions.Cutoff.star_algebraicProjection", "BC4lean.ProperActions.CutoffCoefficients.convolution_mixed_of_normalized", "BC4lean.ProperActions.CutoffCoefficients.involution_mixed"]
  let mut declarations : Array (String × Lean.Name) := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let origin := env.header.moduleNames[idx]!.toString
      if modules.contains origin then
        if info matches .axiomInfo _ then
          throwError "New axiom declaration {name} in {origin}"
        declarations := declarations.push (origin, name)
  Lean.Elab.Command.liftIO <| IO.println "CH7_START|1"
  for (origin, name) in declarations do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom {axiomName} in {name}"
    let axiomText := String.intercalate "," (axioms.toList.map Lean.Name.toString)
    Lean.Elab.Command.liftIO <| IO.println s!"CH7_DECL|{origin}|{name.toString}|{axiomText}"
  for text in (links ++ endpoints).toList.eraseDups do
    let name := text.toName
    unless (env.find? name).isSome do
      throwError "Unknown exact blueprint/endpoint declaration {text}"
    if endpoints.contains text then
      let some idx := env.getModuleIdxFor? name
        | throwError "Missing imported endpoint origin {text}"
      unless modules.contains env.header.moduleNames[idx]!.toString do
        throwError "Required endpoint outside the Chapter 7 declaration scope: {text}"
  for text in links do
    let name := text.toName
    let some idx := env.getModuleIdxFor? name
      | throwError "Missing imported origin for blueprint link {text}"
    let origin := env.header.moduleNames[idx]!.toString
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom {axiomName} in blueprint link {text}"
    let axiomText := String.intercalate "," (axioms.toList.map Lean.Name.toString)
    Lean.Elab.Command.liftIO <| IO.println s!"CH7_LINK|{text}|{origin}|{axiomText}"
  for origin in modules do
    let count := (declarations.filter (·.1 == origin)).size
    Lean.Elab.Command.liftIO <| IO.println s!"CH7_MODULE|{origin}|{count}"
  for text in endpoints do
    let name := text.toName
    let some idx := env.getModuleIdxFor? name
      | throwError "Missing imported endpoint origin {text}"
    let origin := env.header.moduleNames[idx]!.toString
    let axioms ← Lean.collectAxioms name
    let axiomText := String.intercalate "," (axioms.toList.map Lean.Name.toString)
    Lean.Elab.Command.liftIO <| IO.println s!"CH7_ENDPOINT|{text}|{origin}|{axiomText}"
  Lean.Elab.Command.liftIO <| IO.println s!"CH7_END|{declarations.size}|{links.size}|{endpoints.size}"
