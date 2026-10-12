import BC4lean.GradedMatrixMoritaEquivariant
import BC4lean.GradedKasparovCycle
import BC4lean.ModuleTensorCompact
import BC4lean.InteriorModuleTensorCountableGeneration

/-! # Genuine graded cycles tensored with the actual Morita modules

A complete, countably generated graded equivariant correspondence whose
actual left action is compact transports all four localized compact defects
by the actual completed first-factor operator homomorphism. We specialize
this construction to the genuine matrix column and row modules in both
directions. This is a construction of whole raw cycles, with their actual
operators and graded commutators. Quotient transport and inverse cycle
isomorphisms require their own homotopy and associator constructions.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

namespace GradedMatrixMoritaCycle

section TensorCycle

variable {Γ A B C E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}
  (c : GradedKasparovCycle α β δA δB E)
  (η : CStarAlgebraAction Γ C) (δC : CStarGrading C)
  (K : GradedHilbertModule δC F) (V : EquivariantHilbertModule η F)
  (hη : η.PreservesGrading δC) (hV : V.PreservesGrading K)
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (hφJ : ModuleTensorRepresentationGraded (δB := δB) φ K)
  (hφU : ModuleTensorRepresentationEquivariant φ β V)
  (hφcompact : ∀ b, IsModuleCompact (φ b)) (hF : IsCountablyGeneratedModule C F)

/-- All actual cycle data and compact defects are transported by T ↦ T ⊗ 1. -/
def tensorWithCompactLeftAction : GradedKasparovCycle α η δA δC (InteriorModuleTensor (E := E) φ) where
  sourceAction_preservesGrading := c.sourceAction_preservesGrading
  coefficientAction_preservesGrading := hη
  countablyGenerated := c.countablyGenerated.interiorTensor hF φ
  grading := c.grading.interiorTensor K hφJ
  groupAction := c.groupAction.interiorTensor V hφU
  grading_preserved := c.groupAction.interiorTensor_preservesGrading V c.grading K
    c.grading_preserved hV hφU hφJ
  representation := (interiorModuleTensorOperatorHom φ).toNonUnitalStarAlgHom.comp c.representation
  representation_graded a u := by
    let J := (c.grading.interiorTensor K hφJ).grading.toContinuousLinearEquiv.toContinuousLinearMap
    have h : J.comp (interiorModuleTensorOperator φ (c.representation a)).toCLM =
        (interiorModuleTensorOperator φ (c.representation (δA.automorphism a))).toCLM.comp J := by
      apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      intro x y
      change (c.grading.interiorTensor K hφJ).grading
          (interiorModuleTensorOperator φ (c.representation a)
            (interiorModuleTensorMk φ x y)) =
        interiorModuleTensorOperator φ (c.representation (δA.automorphism a))
          ((c.grading.interiorTensor K hφJ).grading (interiorModuleTensorMk φ x y))
      simp only [interiorModuleTensorOperator_mk,
        GradedHilbertModule.interiorTensor_grading_mk, c.representation_graded]
    exact DFunLike.congr_fun h u
  representation_equivariant g a := by
    change (c.groupAction.interiorTensor V hφU).conjugateOperator g
      (interiorModuleTensorOperator φ (c.representation a)) =
      interiorModuleTensorOperator φ (c.representation (α.automorphism g a))
    rw [EquivariantHilbertModule.interiorTensor_conjugateOperator, c.representation_equivariant]
  operator := interiorModuleTensorOperator φ c.operator
  operator_odd := c.operator_odd.interiorModuleTensorOperator K hφJ
  selfadjoint_mod_compact a := by
    have h := (c.selfadjoint_mod_compact a).interiorModuleTensorOperator φ hφcompact
    change IsModuleCompact ((interiorModuleTensorOperator φ c.operator -
      star (interiorModuleTensorOperator φ c.operator)) *
        interiorModuleTensorOperator φ (c.representation a))
    simpa only [← interiorModuleTensorOperatorHom_apply, map_mul, map_sub, map_star] using h
  square_mod_compact a := by
    have h := (c.square_mod_compact a).interiorModuleTensorOperator φ hφcompact
    change IsModuleCompact ((interiorModuleTensorOperator φ c.operator *
      interiorModuleTensorOperator φ c.operator - 1) *
        interiorModuleTensorOperator φ (c.representation a))
    simpa only [← interiorModuleTensorOperatorHom_apply, map_mul, map_sub, map_one] using h
  commutator_compact a := by
    have h := (c.commutator_compact a).interiorModuleTensorOperator φ hφcompact
    change IsModuleCompact (interiorModuleTensorOperator φ c.operator *
      interiorModuleTensorOperator φ (c.representation a) -
        interiorModuleTensorOperator φ (c.representation (δA.automorphism a)) *
          interiorModuleTensorOperator φ c.operator)
    simpa only [← interiorModuleTensorOperatorHom_apply, map_mul, map_sub] using h
  equivariance_mod_compact g a := by
    have h := (c.equivariance_mod_compact g a).interiorModuleTensorOperator φ hφcompact
    change IsModuleCompact
      (((c.groupAction.interiorTensor V hφU).conjugateOperator g
          (interiorModuleTensorOperator φ c.operator) - interiorModuleTensorOperator φ c.operator) *
        interiorModuleTensorOperator φ (c.representation a))
    rw [EquivariantHilbertModule.interiorTensor_conjugateOperator]
    simpa only [← interiorModuleTensorOperatorHom_apply, map_mul, map_sub] using h

/-- Exact degeneracy remains exact under the constructed actual tensor operator map. -/
theorem tensorWithCompactLeftAction_isDegenerate (hc : c.IsDegenerate) :
    (tensorWithCompactLeftAction c η δC K V hη hV φ hφJ hφU hφcompact hF).IsDegenerate := by
  rcases hc with ⟨hself, hsquare, hcomm, heq⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    have h := congrArg (interiorModuleTensorOperatorHom φ) (hself a)
    change (interiorModuleTensorOperator φ c.operator -
      star (interiorModuleTensorOperator φ c.operator)) *
        interiorModuleTensorOperator φ (c.representation a) = 0
    simpa only [map_mul, map_sub, map_star, map_zero,
      interiorModuleTensorOperatorHom_apply] using h
  · intro a
    have h := congrArg (interiorModuleTensorOperatorHom φ) (hsquare a)
    change (interiorModuleTensorOperator φ c.operator *
      interiorModuleTensorOperator φ c.operator - 1) *
        interiorModuleTensorOperator φ (c.representation a) = 0
    simpa only [map_mul, map_sub, map_one, map_zero,
      interiorModuleTensorOperatorHom_apply] using h
  · intro a
    have h := congrArg (interiorModuleTensorOperatorHom φ) (hcomm a)
    change interiorModuleTensorOperator φ c.operator *
      interiorModuleTensorOperator φ (c.representation a) -
        interiorModuleTensorOperator φ (c.representation (δA.automorphism a)) *
          interiorModuleTensorOperator φ c.operator = 0
    simpa only [map_mul, map_sub, map_zero, interiorModuleTensorOperatorHom_apply] using h
  · intro g a
    have h := congrArg (interiorModuleTensorOperatorHom φ) (heq g a)
    change ((c.groupAction.interiorTensor V hφU).conjugateOperator g
      (interiorModuleTensorOperator φ c.operator) - interiorModuleTensorOperator φ c.operator) *
        interiorModuleTensorOperator φ (c.representation a) = 0
    rw [EquivariantHilbertModule.interiorTensor_conjugateOperator]
    simpa only [map_mul, map_sub, map_zero, interiorModuleTensorOperatorHom_apply] using h

end TensorCycle

variable {Γ A B : Type*} [Group Γ] [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {δA : CStarGrading A}

open GradedMatrixMoritaEquivariant

def matrixToCoefficient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul (GradedMatrixMoritaMatrix B)ᵐᵒᵖ E] [CStarModule (GradedMatrixMoritaMatrix B)ᵐᵒᵖ E]
    [CompleteSpace E] (β : CStarAlgebraAction Γ B)
    (c : GradedKasparovCycle α (matrixAction β) δA GradedMatrixMoritaMatrix.grading E) :
    GradedKasparovCycle α β δA CStarGrading.trivial
      (InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B)
        (GradedMatrixMoritaColumn.leftAction (B := B))) :=
  tensorWithCompactLeftAction (B := GradedMatrixMoritaMatrix B) (C := B)
    (E := E) (F := GradedMatrixMoritaColumn B) c β CStarGrading.trivial GradedMatrixMoritaColumn.grading
    (columnAction β) β.preservesGrading_trivial (columnAction_preservesGrading β)
    GradedMatrixMoritaColumn.leftAction GradedMatrixMoritaColumn.leftAction_graded
    (columnRepresentation_equivariant β) GradedMatrixMoritaColumn.leftAction_compact
    GradedMatrixMoritaColumn.countablyGenerated

def coefficientToMatrix {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E] (β : CStarAlgebraAction Γ B)
    (c : GradedKasparovCycle α β δA CStarGrading.trivial E) :
    GradedKasparovCycle α (matrixAction β) δA GradedMatrixMoritaMatrix.grading
      (InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B)
        (GradedMatrixMoritaRow.leftAction (B := B))) :=
  tensorWithCompactLeftAction (B := B) (C := GradedMatrixMoritaMatrix B)
    (E := E) (F := GradedMatrixMoritaRow B) c (matrixAction β) GradedMatrixMoritaMatrix.grading
    GradedMatrixMoritaRow.grading (rowAction β) (matrixAction_preservesGrading β)
    (rowAction_preservesGrading β) GradedMatrixMoritaRow.leftAction
    GradedMatrixMoritaRow.leftAction_graded (rowRepresentation_equivariant β)
    GradedMatrixMoritaRow.leftAction_compact GradedMatrixMoritaRow.countablyGenerated

end GradedMatrixMoritaCycle
end BC4lean.KKTheory
