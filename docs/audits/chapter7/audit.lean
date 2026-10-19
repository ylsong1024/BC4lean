import BC4lean.AlgebraicCrossedProduct
import BC4lean.AlgebraicCrossedProductMap
import BC4lean.AlgebraicCrossedRepresentation
import BC4lean.ArbitraryHilbertModuleSum
import BC4lean.AssemblyCofinalIndex
import BC4lean.AssemblyColimit
import BC4lean.AssemblyCutoffNaturality
import BC4lean.AssemblyModelNaturality
import BC4lean.AssemblyPieceHom
import BC4lean.AssemblyProperNaturality
import BC4lean.AssemblyTransition
import BC4lean.CliffordPairStandardTensorCompatibility
import BC4lean.CocompactPieceCutoff
import BC4lean.CovariantAlgebraicRepresentation
import BC4lean.CutoffAlgebraicProjection
import BC4lean.CutoffCoefficientProjection
import BC4lean.CutoffProperPullbackNaturality
import BC4lean.CutoffRestrictionNaturality
import BC4lean.EssentialModulePositivityClosed
import BC4lean.GradedKasparovRegrade
import BC4lean.IndexedHilbertModuleIsometry
import BC4lean.IndexedHilbertModuleTensor
import BC4lean.IndexedStandardReducedCrossedEquiv
import BC4lean.InteriorModuleTensorFaithful
import BC4lean.InteriorModuleTensorScalarExtension
import BC4lean.InteriorModuleTensorScalarExtensionGrading
import BC4lean.InteriorModuleTensorSecondFactorIsometry
import BC4lean.KasparovDescentAction
import BC4lean.KasparovDescentAlgebraicRepresentation
import BC4lean.KasparovDescentClass
import BC4lean.KasparovDescentCliffordExpansionIso
import BC4lean.KasparovDescentCliffordExternalEvenIso
import BC4lean.KasparovDescentCliffordPair
import BC4lean.KasparovDescentCliffordSignedSource
import BC4lean.KasparovDescentCliffordSignedSourceIso
import BC4lean.KasparovDescentCompactAction
import BC4lean.KasparovDescentConnection
import BC4lean.KasparovDescentCycleIso
import BC4lean.KasparovDescentDirectSum
import BC4lean.KasparovDescentEvenGradedCoherence
import BC4lean.KasparovDescentEvenProduct
import BC4lean.KasparovDescentFullHomotopy
import BC4lean.KasparovDescentGeneratorDefects
import BC4lean.KasparovDescentGradedClass
import BC4lean.KasparovDescentGradedClassProduct
import BC4lean.KasparovDescentGradedCycle
import BC4lean.KasparovDescentGradedCycleIso
import BC4lean.KasparovDescentGradedDirectSum
import BC4lean.KasparovDescentGradedFullHomotopy
import BC4lean.KasparovDescentGradedIntervalCycle
import BC4lean.KasparovDescentGradedIntervalGrading
import BC4lean.KasparovDescentGradedProduct
import BC4lean.KasparovDescentGradedProductClass
import BC4lean.KasparovDescentGrading
import BC4lean.KasparovDescentIntervalCycle
import BC4lean.KasparovDescentIntervalDefects
import BC4lean.KasparovDescentIntervalFibreIso
import BC4lean.KasparovDescentIntervalModule
import BC4lean.KasparovDescentIntervalNorm
import BC4lean.KasparovDescentIntervalRepresentation
import BC4lean.KasparovDescentModule
import BC4lean.KasparovDescentNativeClassCoherence
import BC4lean.KasparovDescentNativeClassMaps
import BC4lean.KasparovDescentNativeParityProduct
import BC4lean.KasparovDescentOperatorDefects
import BC4lean.KasparovDescentPairCoefficientEquiv
import BC4lean.KasparovDescentProductPositivity
import BC4lean.KasparovDescentRawCycle
import BC4lean.KasparovDescentReducedRepresentation
import BC4lean.KasparovDescentRegularEmbedding
import BC4lean.KasparovDescentSourcePullback
import BC4lean.KasparovDescentSourcePullbackClass
import BC4lean.KasparovDescentTensorComparison
import BC4lean.KasparovDescentTensorComparisonGrading
import BC4lean.KasparovDescentTensorComparisonSource
import BC4lean.NativeEvenSourcePullback
import BC4lean.NativeOddSourcePullback
import BC4lean.NonunitalProjectionK0
import BC4lean.ProperCutoffFunction
import BC4lean.RectangularInteriorModuleTensorCompact
import BC4lean.ReducedCrossedCoefficientApproximateUnit
import BC4lean.ReducedCrossedCompactDefects
import BC4lean.ReducedCrossedGradingOperators
import BC4lean.ReducedCrossedHilbertGrading
import BC4lean.ReducedCrossedHilbertModule
import BC4lean.ReducedCrossedLeftRegular
import BC4lean.ReducedCrossedNorm
import BC4lean.ReducedCrossedProduct
import BC4lean.ReducedCrossedProductGrading
import BC4lean.ReducedCrossedProductMap
import BC4lean.ReducedCrossedProductPair
import BC4lean.ReducedCrossedRegularOperators
import BC4lean.ReducedCrossedRepresentationExtension
import BC4lean.ReducedCrossedScalarHilbert
import BC4lean.ReducedCrossedScalarProduct
import BC4lean.ReducedCutoffProjection
import BC4lean.ReducedRegularTensorEmbedding
import BC4lean.ReducedScalarKKComparison
import BC4lean.ReducedSourceRegularBound
import BC4lean.ReducedSourceRegularOperator
import BC4lean.ReducedSourceTensorEmbedding
import BC4lean.ScalarKKNativeNaturality
import BC4lean.StandardCoefficientExtensionEquiv
import BC4lean.StandardModuleTensorEmbedding
import BC4lean.TrivialActionUnitary
import Lean
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let modules : Array String := #["BC4lean.AlgebraicCrossedProduct", "BC4lean.AlgebraicCrossedProductMap", "BC4lean.AlgebraicCrossedRepresentation", "BC4lean.ArbitraryHilbertModuleSum", "BC4lean.AssemblyCofinalIndex", "BC4lean.AssemblyColimit", "BC4lean.AssemblyCutoffNaturality", "BC4lean.AssemblyModelNaturality", "BC4lean.AssemblyPieceHom", "BC4lean.AssemblyProperNaturality", "BC4lean.AssemblyTransition", "BC4lean.CliffordPairStandardTensorCompatibility", "BC4lean.CocompactPieceCutoff", "BC4lean.CovariantAlgebraicRepresentation", "BC4lean.CutoffAlgebraicProjection", "BC4lean.CutoffCoefficientProjection", "BC4lean.CutoffProperPullbackNaturality", "BC4lean.CutoffRestrictionNaturality", "BC4lean.EssentialModulePositivityClosed", "BC4lean.GradedKasparovRegrade", "BC4lean.IndexedHilbertModuleIsometry", "BC4lean.IndexedHilbertModuleTensor", "BC4lean.IndexedStandardReducedCrossedEquiv", "BC4lean.InteriorModuleTensorFaithful", "BC4lean.InteriorModuleTensorScalarExtension", "BC4lean.InteriorModuleTensorScalarExtensionGrading", "BC4lean.InteriorModuleTensorSecondFactorIsometry", "BC4lean.KasparovDescentAction", "BC4lean.KasparovDescentAlgebraicRepresentation", "BC4lean.KasparovDescentClass", "BC4lean.KasparovDescentCliffordExpansionIso", "BC4lean.KasparovDescentCliffordExternalEvenIso", "BC4lean.KasparovDescentCliffordPair", "BC4lean.KasparovDescentCliffordSignedSource", "BC4lean.KasparovDescentCliffordSignedSourceIso", "BC4lean.KasparovDescentCompactAction", "BC4lean.KasparovDescentConnection", "BC4lean.KasparovDescentCycleIso", "BC4lean.KasparovDescentDirectSum", "BC4lean.KasparovDescentEvenGradedCoherence", "BC4lean.KasparovDescentEvenProduct", "BC4lean.KasparovDescentFullHomotopy", "BC4lean.KasparovDescentGeneratorDefects", "BC4lean.KasparovDescentGradedClass", "BC4lean.KasparovDescentGradedClassProduct", "BC4lean.KasparovDescentGradedCycle", "BC4lean.KasparovDescentGradedCycleIso", "BC4lean.KasparovDescentGradedDirectSum", "BC4lean.KasparovDescentGradedFullHomotopy", "BC4lean.KasparovDescentGradedIntervalCycle", "BC4lean.KasparovDescentGradedIntervalGrading", "BC4lean.KasparovDescentGradedProduct", "BC4lean.KasparovDescentGradedProductClass", "BC4lean.KasparovDescentGrading", "BC4lean.KasparovDescentIntervalCycle", "BC4lean.KasparovDescentIntervalDefects", "BC4lean.KasparovDescentIntervalFibreIso", "BC4lean.KasparovDescentIntervalModule", "BC4lean.KasparovDescentIntervalNorm", "BC4lean.KasparovDescentIntervalRepresentation", "BC4lean.KasparovDescentModule", "BC4lean.KasparovDescentNativeClassCoherence", "BC4lean.KasparovDescentNativeClassMaps", "BC4lean.KasparovDescentNativeParityProduct", "BC4lean.KasparovDescentOperatorDefects", "BC4lean.KasparovDescentPairCoefficientEquiv", "BC4lean.KasparovDescentProductPositivity", "BC4lean.KasparovDescentRawCycle", "BC4lean.KasparovDescentReducedRepresentation", "BC4lean.KasparovDescentRegularEmbedding", "BC4lean.KasparovDescentSourcePullback", "BC4lean.KasparovDescentSourcePullbackClass", "BC4lean.KasparovDescentTensorComparison", "BC4lean.KasparovDescentTensorComparisonGrading", "BC4lean.KasparovDescentTensorComparisonSource", "BC4lean.NativeEvenSourcePullback", "BC4lean.NativeOddSourcePullback", "BC4lean.NonunitalProjectionK0", "BC4lean.ProperCutoffFunction", "BC4lean.RectangularInteriorModuleTensorCompact", "BC4lean.ReducedCrossedCoefficientApproximateUnit", "BC4lean.ReducedCrossedCompactDefects", "BC4lean.ReducedCrossedGradingOperators", "BC4lean.ReducedCrossedHilbertGrading", "BC4lean.ReducedCrossedHilbertModule", "BC4lean.ReducedCrossedLeftRegular", "BC4lean.ReducedCrossedNorm", "BC4lean.ReducedCrossedProduct", "BC4lean.ReducedCrossedProductGrading", "BC4lean.ReducedCrossedProductMap", "BC4lean.ReducedCrossedProductPair", "BC4lean.ReducedCrossedRegularOperators", "BC4lean.ReducedCrossedRepresentationExtension", "BC4lean.ReducedCrossedScalarHilbert", "BC4lean.ReducedCrossedScalarProduct", "BC4lean.ReducedCutoffProjection", "BC4lean.ReducedRegularTensorEmbedding", "BC4lean.ReducedScalarKKComparison", "BC4lean.ReducedSourceRegularBound", "BC4lean.ReducedSourceRegularOperator", "BC4lean.ReducedSourceTensorEmbedding", "BC4lean.ScalarKKNativeNaturality", "BC4lean.StandardCoefficientExtensionEquiv", "BC4lean.StandardModuleTensorEmbedding", "BC4lean.TrivialActionUnitary"]
  let links : Array String := #["BC4lean.Assembly.assemblyEvenHom", "BC4lean.Assembly.assemblyHom", "BC4lean.Assembly.assemblyHom_cofinalIndexEquiv", "BC4lean.Assembly.assemblyHom_comp_pushforward", "BC4lean.Assembly.assemblyHom_homotopyEquiv", "BC4lean.Assembly.assemblyHom_ofPiece", "BC4lean.Assembly.assemblyHom_reindex", "BC4lean.Assembly.assemblyHom_unique", "BC4lean.Assembly.assemblyHom_universalModelEquiv", "BC4lean.Assembly.assemblyOddHom", "BC4lean.Assembly.cutoffKKClass", "BC4lean.Assembly.cutoffProductHom", "BC4lean.Assembly.indexedAssemblyHom", "BC4lean.Assembly.indexedAssemblyHom_cofinalComparisonEquiv", "BC4lean.Assembly.indexedAssemblyHom_of", "BC4lean.Assembly.pieceAssemblyEvenHom", "BC4lean.Assembly.pieceAssemblyHom", "BC4lean.Assembly.pieceAssemblyHom_boundedMap", "BC4lean.Assembly.pieceAssemblyHom_eq_of_cutoff", "BC4lean.Assembly.pieceAssemblyHom_transition", "BC4lean.Assembly.pieceAssemblyOddHom", "BC4lean.Assembly.reducedAssemblyEvenHom", "BC4lean.Assembly.reducedAssemblyHom", "BC4lean.Assembly.reducedAssemblyOddHom", "BC4lean.Assembly.reducedScalarKKToAnalyticHom", "BC4lean.Assembly.spaceAssemblyHom", "BC4lean.Assembly.spaceAssemblyHom_independent", "BC4lean.KKTheory.AlgebraicCrossedProduct", "BC4lean.KKTheory.AlgebraicCrossedProduct.coeff_mul", "BC4lean.KKTheory.AlgebraicCrossedProduct.coeff_star", "BC4lean.KKTheory.EquivariantHilbertModule.adjointableAction", "BC4lean.KKTheory.EquivariantHilbertModule.compactOperatorAction", "BC4lean.KKTheory.EquivariantHilbertModule.compactOperatorAction_equivariant", "BC4lean.KKTheory.EquivariantHilbertModule.compactOperatorAction_rankOne", "BC4lean.KKTheory.KasparovDescent.Module", "BC4lean.KKTheory.KasparovDescent.algebraicSourceOperator_norm_le", "BC4lean.KKTheory.KasparovDescent.classHom", "BC4lean.KKTheory.KasparovDescent.classHom_product", "BC4lean.KKTheory.KasparovDescent.classHom_sourcePullback", "BC4lean.KKTheory.KasparovDescent.coefficientRepresentation", "BC4lean.KKTheory.KasparovDescent.countablyGenerated", "BC4lean.KKTheory.KasparovDescent.descended_gradedConnection", "BC4lean.KKTheory.KasparovDescent.descended_isGradedProduct", "BC4lean.KKTheory.KasparovDescent.evenClassHom", "BC4lean.KKTheory.KasparovDescent.evenClassHom_evenProduct", "BC4lean.KKTheory.KasparovDescent.evenClassHom_oddOddProduct", "BC4lean.KKTheory.KasparovDescent.evenClass_mk", "BC4lean.KKTheory.KasparovDescent.evenFullHomotopy", "BC4lean.KKTheory.KasparovDescent.gradedFullHomotopy", "BC4lean.KKTheory.KasparovDescent.mk_balance", "BC4lean.KKTheory.KasparovDescent.mk_inner", "BC4lean.KKTheory.KasparovDescent.norm_operatorHom_le", "BC4lean.KKTheory.KasparovDescent.oddClassHom", "BC4lean.KKTheory.KasparovDescent.oddClassHom_evenOddProduct", "BC4lean.KKTheory.KasparovDescent.oddClassHom_oddEvenProduct", "BC4lean.KKTheory.KasparovDescent.oddClass_mk", "BC4lean.KKTheory.KasparovDescent.oddFullHomotopy", "BC4lean.KKTheory.KasparovDescent.operatorHom_adjoint", "BC4lean.KKTheory.KasparovDescent.operatorHom_compact", "BC4lean.KKTheory.KasparovDescent.operatorHom_mk", "BC4lean.KKTheory.KasparovDescent.reducedSourceRepresentation", "BC4lean.KKTheory.KasparovDescent.reducedSourceRepresentation_quadratic_positive", "BC4lean.KKTheory.KasparovDescent.reducedSourceRepresentation_single", "BC4lean.KKTheory.KasparovDescent.tensorComparison", "BC4lean.KKTheory.ReducedCrossedHilbertModule", "BC4lean.KKTheory.ReducedCrossedProduct", "BC4lean.KKTheory.algebraicCrossedOperatorHom_eq_sum", "BC4lean.KKTheory.algebraicCrossedReducedNorm", "BC4lean.KKTheory.algebraicCrossedReducedNorm_cstar", "BC4lean.KKTheory.algebraicCrossedReducedNorm_eq_zero", "BC4lean.KKTheory.algebraicToReducedCrossed", "BC4lean.KKTheory.algebraicToReducedCrossed_denseRange", "BC4lean.KKTheory.algebraicToReducedCrossed_injective", "BC4lean.KKTheory.coefficientToReducedCrossed", "BC4lean.KKTheory.norm_coefficientToReducedCrossed", "BC4lean.KKTheory.norm_reducedCrossedCoefficient", "BC4lean.KKTheory.reducedCrossedAlgebra_coe_eq_closure_span", "BC4lean.KKTheory.reducedCrossedCoefficient", "BC4lean.KKTheory.reducedCrossedEvaluation_coefficient", "BC4lean.KKTheory.reducedCrossedEvaluation_regular", "BC4lean.KKTheory.reducedCrossedFiniteInner_self_eq_zero_iff", "BC4lean.KKTheory.reducedCrossedMap", "BC4lean.KKTheory.reducedCrossedMap_comp", "BC4lean.KKTheory.reducedCrossedMk_denseRange", "BC4lean.KKTheory.reducedCrossedMk_norm_coefficients", "BC4lean.KKTheory.reducedCrossedProduct_nonUnitalCStarAlgebra", "BC4lean.KKTheory.reducedCrossedProduct_separableSpace", "BC4lean.KKTheory.reducedCrossedRegular", "BC4lean.KKTheory.reducedCrossedScalarHilbertEquiv", "BC4lean.KKTheory.reducedCrossedScalarOperatorEquiv_generator", "BC4lean.KKTheory.reducedCrossedScalarProductEquiv", "BC4lean.KKTheory.reducedCrossedScalarProductEquiv_oneCoefficient", "BC4lean.KKTheory.reducedCrossed_covariance", "BC4lean.OperatorKTheory.nonunitalProjectionK0", "BC4lean.OperatorKTheory.nonunitalProjectionK0_eq_of_partialIsometry", "BC4lean.OperatorKTheory.operatorK0Inclusion_nonunitalProjectionK0", "BC4lean.ProperActions.CocompactPiece.exists_cutoffFunction", "BC4lean.ProperActions.CocompactPiece.proper", "BC4lean.ProperActions.Cutoff.CutoffFunction", "BC4lean.ProperActions.Cutoff.algebraicProjection", "BC4lean.ProperActions.Cutoff.algebraicProjection_mul_self", "BC4lean.ProperActions.Cutoff.coeff_mixedAlgebraic", "BC4lean.ProperActions.Cutoff.cutoffK0", "BC4lean.ProperActions.Cutoff.cutoffK0_independent", "BC4lean.ProperActions.Cutoff.cutoffK0_pieceRestriction", "BC4lean.ProperActions.Cutoff.cutoffK0_properPullback", "BC4lean.ProperActions.Cutoff.exists_cutoffFunction", "BC4lean.ProperActions.Cutoff.finite_mixedCoefficient_support", "BC4lean.ProperActions.Cutoff.mixedAlgebraic", "BC4lean.ProperActions.Cutoff.mixedAlgebraic_partialIsometry", "BC4lean.ProperActions.Cutoff.normalized_tsum", "BC4lean.ProperActions.Cutoff.reducedCutoffProjection", "BC4lean.ProperActions.Cutoff.reducedCutoffProjection_isStarProjection", "BC4lean.ProperActions.Cutoff.reducedCutoffProjection_partialIsometry", "BC4lean.ProperActions.Cutoff.star_algebraicProjection", "BC4lean.ProperActions.CutoffCoefficients.convolution_mixed_of_normalized", "BC4lean.ProperActions.CutoffCoefficients.involution_mixed"]
  let endpoints : Array String := #["BC4lean.Assembly.assemblyEvenHom", "BC4lean.Assembly.assemblyHom", "BC4lean.Assembly.assemblyHom_cofinalIndexEquiv", "BC4lean.Assembly.assemblyHom_comp_pushforward", "BC4lean.Assembly.assemblyHom_homotopyEquiv", "BC4lean.Assembly.assemblyHom_ofPiece", "BC4lean.Assembly.assemblyHom_reindex", "BC4lean.Assembly.assemblyHom_unique", "BC4lean.Assembly.assemblyHom_universalModelEquiv", "BC4lean.Assembly.assemblyOddHom", "BC4lean.Assembly.cutoffKKClass", "BC4lean.Assembly.cutoffProductHom", "BC4lean.Assembly.indexedAssemblyHom", "BC4lean.Assembly.indexedAssemblyHom_cofinalComparisonEquiv", "BC4lean.Assembly.indexedAssemblyHom_of", "BC4lean.Assembly.pieceAssemblyEvenHom", "BC4lean.Assembly.pieceAssemblyHom", "BC4lean.Assembly.pieceAssemblyHom_boundedMap", "BC4lean.Assembly.pieceAssemblyHom_eq_of_cutoff", "BC4lean.Assembly.pieceAssemblyHom_transition", "BC4lean.Assembly.pieceAssemblyOddHom", "BC4lean.Assembly.reducedAssemblyEvenHom", "BC4lean.Assembly.reducedAssemblyHom", "BC4lean.Assembly.reducedAssemblyOddHom", "BC4lean.Assembly.reducedScalarKKToAnalyticHom", "BC4lean.Assembly.spaceAssemblyHom", "BC4lean.Assembly.spaceAssemblyHom_independent", "BC4lean.KKTheory.AlgebraicCrossedProduct", "BC4lean.KKTheory.AlgebraicCrossedProduct.coeff_mul", "BC4lean.KKTheory.AlgebraicCrossedProduct.coeff_star", "BC4lean.KKTheory.EquivariantHilbertModule.adjointableAction", "BC4lean.KKTheory.EquivariantHilbertModule.compactOperatorAction", "BC4lean.KKTheory.EquivariantHilbertModule.compactOperatorAction_equivariant", "BC4lean.KKTheory.EquivariantHilbertModule.compactOperatorAction_rankOne", "BC4lean.KKTheory.KasparovDescent.Module", "BC4lean.KKTheory.KasparovDescent.algebraicSourceOperator_norm_le", "BC4lean.KKTheory.KasparovDescent.classHom", "BC4lean.KKTheory.KasparovDescent.classHom_product", "BC4lean.KKTheory.KasparovDescent.classHom_sourcePullback", "BC4lean.KKTheory.KasparovDescent.coefficientRepresentation", "BC4lean.KKTheory.KasparovDescent.countablyGenerated", "BC4lean.KKTheory.KasparovDescent.descended_gradedConnection", "BC4lean.KKTheory.KasparovDescent.descended_isGradedProduct", "BC4lean.KKTheory.KasparovDescent.evenClassHom", "BC4lean.KKTheory.KasparovDescent.evenClassHom_evenProduct", "BC4lean.KKTheory.KasparovDescent.evenClassHom_oddOddProduct", "BC4lean.KKTheory.KasparovDescent.evenClass_mk", "BC4lean.KKTheory.KasparovDescent.evenFullHomotopy", "BC4lean.KKTheory.KasparovDescent.gradedFullHomotopy", "BC4lean.KKTheory.KasparovDescent.mk_balance", "BC4lean.KKTheory.KasparovDescent.mk_inner", "BC4lean.KKTheory.KasparovDescent.norm_operatorHom_le", "BC4lean.KKTheory.KasparovDescent.oddClassHom", "BC4lean.KKTheory.KasparovDescent.oddClassHom_evenOddProduct", "BC4lean.KKTheory.KasparovDescent.oddClassHom_oddEvenProduct", "BC4lean.KKTheory.KasparovDescent.oddClass_mk", "BC4lean.KKTheory.KasparovDescent.oddFullHomotopy", "BC4lean.KKTheory.KasparovDescent.operatorHom_adjoint", "BC4lean.KKTheory.KasparovDescent.operatorHom_compact", "BC4lean.KKTheory.KasparovDescent.operatorHom_mk", "BC4lean.KKTheory.KasparovDescent.reducedSourceRepresentation", "BC4lean.KKTheory.KasparovDescent.reducedSourceRepresentation_quadratic_positive", "BC4lean.KKTheory.KasparovDescent.reducedSourceRepresentation_single", "BC4lean.KKTheory.KasparovDescent.tensorComparison", "BC4lean.KKTheory.ReducedCrossedHilbertModule", "BC4lean.KKTheory.ReducedCrossedProduct", "BC4lean.KKTheory.algebraicCrossedOperatorHom_eq_sum", "BC4lean.KKTheory.algebraicCrossedReducedNorm", "BC4lean.KKTheory.algebraicCrossedReducedNorm_cstar", "BC4lean.KKTheory.algebraicCrossedReducedNorm_eq_zero", "BC4lean.KKTheory.algebraicToReducedCrossed", "BC4lean.KKTheory.algebraicToReducedCrossed_denseRange", "BC4lean.KKTheory.algebraicToReducedCrossed_injective", "BC4lean.KKTheory.coefficientToReducedCrossed", "BC4lean.KKTheory.norm_coefficientToReducedCrossed", "BC4lean.KKTheory.norm_reducedCrossedCoefficient", "BC4lean.KKTheory.reducedCrossedAlgebra_coe_eq_closure_span", "BC4lean.KKTheory.reducedCrossedCoefficient", "BC4lean.KKTheory.reducedCrossedEvaluation_coefficient", "BC4lean.KKTheory.reducedCrossedEvaluation_regular", "BC4lean.KKTheory.reducedCrossedFiniteInner_self_eq_zero_iff", "BC4lean.KKTheory.reducedCrossedMap", "BC4lean.KKTheory.reducedCrossedMap_comp", "BC4lean.KKTheory.reducedCrossedMk_denseRange", "BC4lean.KKTheory.reducedCrossedMk_norm_coefficients", "BC4lean.KKTheory.reducedCrossedProduct_nonUnitalCStarAlgebra", "BC4lean.KKTheory.reducedCrossedProduct_separableSpace", "BC4lean.KKTheory.reducedCrossedRegular", "BC4lean.KKTheory.reducedCrossedScalarHilbertEquiv", "BC4lean.KKTheory.reducedCrossedScalarOperatorEquiv_generator", "BC4lean.KKTheory.reducedCrossedScalarProductEquiv", "BC4lean.KKTheory.reducedCrossedScalarProductEquiv_oneCoefficient", "BC4lean.KKTheory.reducedCrossed_covariance", "BC4lean.OperatorKTheory.nonunitalProjectionK0", "BC4lean.OperatorKTheory.nonunitalProjectionK0_eq_of_partialIsometry", "BC4lean.OperatorKTheory.operatorK0Inclusion_nonunitalProjectionK0", "BC4lean.ProperActions.CocompactPiece.exists_cutoffFunction", "BC4lean.ProperActions.CocompactPiece.proper", "BC4lean.ProperActions.Cutoff.CutoffFunction", "BC4lean.ProperActions.Cutoff.algebraicProjection", "BC4lean.ProperActions.Cutoff.algebraicProjection_mul_self", "BC4lean.ProperActions.Cutoff.coeff_mixedAlgebraic", "BC4lean.ProperActions.Cutoff.cutoffK0", "BC4lean.ProperActions.Cutoff.cutoffK0_independent", "BC4lean.ProperActions.Cutoff.cutoffK0_pieceRestriction", "BC4lean.ProperActions.Cutoff.cutoffK0_properPullback", "BC4lean.ProperActions.Cutoff.exists_cutoffFunction", "BC4lean.ProperActions.Cutoff.finite_mixedCoefficient_support", "BC4lean.ProperActions.Cutoff.mixedAlgebraic", "BC4lean.ProperActions.Cutoff.mixedAlgebraic_partialIsometry", "BC4lean.ProperActions.Cutoff.normalized_tsum", "BC4lean.ProperActions.Cutoff.reducedCutoffProjection", "BC4lean.ProperActions.Cutoff.reducedCutoffProjection_isStarProjection", "BC4lean.ProperActions.Cutoff.reducedCutoffProjection_partialIsometry", "BC4lean.ProperActions.Cutoff.star_algebraicProjection", "BC4lean.ProperActions.CutoffCoefficients.convolution_mixed_of_normalized", "BC4lean.ProperActions.CutoffCoefficients.involution_mixed"]
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
