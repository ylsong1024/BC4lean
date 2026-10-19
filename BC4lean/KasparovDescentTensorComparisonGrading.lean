import BC4lean.KasparovDescentTensorComparison
import BC4lean.InteriorModuleTensorScalarExtensionGrading
import BC4lean.KasparovDescentGradedCycle

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual grading compatibility of the crossed tensor comparison

This instantiates the
proved-form scalar-extension grading lemma and the genuine associator's
grading theorem. It retains arbitrary coefficient gradings and the actual
graded, possibly degenerate second Kasparov representation.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent

variable {Γ B C E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F]
  [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
  {δB : CStarGrading B} {δC : CStarGrading C}
  (β : CStarAlgebraAction Γ B) (γ : CStarAlgebraAction Γ C)
  (J : GradedHilbertModule δB E)
  (d : GradedKasparovCycle β γ δB δC F)

private theorem tensorComparison_coefficient_mk_aux
    (x : E) (a : (ReducedCrossedProduct β)ᵐᵒᵖ) (z : Module γ F) :
    tensorCoefficientExtensionEquiv (E := E) β γ d.groupAction d.representation
        d.representation_equivariant
        (interiorModuleTensorMk
          (reducedSourceRepresentation γ F β d.groupAction d.representation
            d.representation_equivariant) (mk β E x a) z) =
      interiorModuleTensorMk
        (InteriorModuleTensorAssociator.rightRepresentation d.representation
          (coefficientRepresentation γ)) x
        (reducedSourceRepresentation γ F β d.groupAction d.representation
          d.representation_equivariant (MulOpposite.unop a) z) := by
  let ρ := reducedSourceRepresentation γ F β d.groupAction d.representation
    d.representation_equivariant
  let ψ := InteriorModuleTensorAssociator.rightRepresentation d.representation
    (coefficientRepresentation γ)
  let e := tensorCoefficientExtensionEquiv (E := E) β γ d.groupAction
    d.representation d.representation_equivariant
  let W : HilbertModuleEquiv (ReducedCrossedProduct γ)
      (Module γ (InteriorModuleTensor (E := E) d.representation))
      (InteriorModuleTensor (E := E) ψ) :=
    InteriorModuleTensorAssociator.hilbertEquiv
      (B := B) (C := C) (D := ReducedCrossedProduct γ)
      (E := E) (F := F) (G := (ReducedCrossedProduct γ)ᵐᵒᵖ)
      d.representation (coefficientRepresentation γ)
  have hfactor :
      W (tensorComparison β γ d.groupAction d.representation
        d.representation_equivariant (interiorModuleTensorMk ρ (mk β E x a) z)) =
        e (interiorModuleTensorMk ρ (mk β E x a) z) :=
    W.apply_symm_apply (e (interiorModuleTensorMk ρ (mk β E x a) z))
  have hpure := congrArg
    (fun v : Module γ (InteriorModuleTensor (E := E) d.representation) => W v)
    (tensorComparison_mk (Γ := Γ) (B := B) (C := C) (E := E) (F := F)
      β γ d.groupAction d.representation d.representation_equivariant x a z)
  exact hfactor.symm.trans (hpure.trans
    (W.apply_symm_apply (interiorModuleTensorMk ψ x (ρ (MulOpposite.unop a) z))))

private def tensorComparisonGradingRho :=
  reducedSourceRepresentation γ F β d.groupAction d.representation
    d.representation_equivariant

private def tensorComparisonGradingPsi :=
  InteriorModuleTensorAssociator.rightRepresentation d.representation
    (coefficientRepresentation γ)

private def tensorComparisonGradingK :=
  moduleGrading γ δC d.coefficientAction_preservesGrading d.grading

private def tensorComparisonGradingJB :=
  moduleGrading β δB d.sourceAction_preservesGrading J

private theorem tensorComparisonGradingRho_graded :
    ModuleTensorRepresentationGraded
      (δB := reducedCrossedProductGrading β δB d.sourceAction_preservesGrading)
      (tensorComparisonGradingRho β γ d) (tensorComparisonGradingK β γ d) :=
  fun b v => reducedSourceRepresentation_graded γ β d b v

omit [PartialOrder B] [StarOrderedRing B] in
private theorem tensorComparisonGradingPsi_graded :
    ModuleTensorRepresentationGraded (δB := δB)
      (tensorComparisonGradingPsi β γ d) (tensorComparisonGradingK β γ d) :=
  InteriorModuleTensorAssociator.rightRepresentation_graded
    (B := B) (C := C) (D := ReducedCrossedProduct γ)
    (F := F) (G := (ReducedCrossedProduct γ)ᵐᵒᵖ)
    d.representation (coefficientRepresentation γ) d.grading
    (crossedStandardGrading γ δC d.coefficientAction_preservesGrading)
    d.representation_graded
    (coefficientRepresentation_graded γ δC d.coefficientAction_preservesGrading)

private def tensorComparisonGradingSource :=
  (tensorComparisonGradingJB β γ J d).interiorTensor
    (tensorComparisonGradingK β γ d) (tensorComparisonGradingRho_graded β γ d)

private abbrev tensorComparisonGradingMiddleCarrier :=
  InteriorModuleTensor (E := E)
    (InteriorModuleTensorAssociator.rightRepresentation d.representation
      (coefficientRepresentation γ))

private def tensorComparisonGradingMiddle :
    GradedHilbertModule
      (reducedCrossedProductGrading γ δC d.coefficientAction_preservesGrading)
      (tensorComparisonGradingMiddleCarrier (E := E) β γ d) :=
  GradedHilbertModule.interiorTensor
    (B := B) (C := ReducedCrossedProduct γ) (E := E)
    (F := InteriorModuleTensor (E := F) (coefficientRepresentation γ))
    (φ := InteriorModuleTensorAssociator.rightRepresentation d.representation
      (coefficientRepresentation γ))
    J (tensorComparisonGradingK β γ d) (tensorComparisonGradingPsi_graded β γ d)

private def tensorComparisonGradingTarget :=
  moduleGrading γ δC d.coefficientAction_preservesGrading
    (J.interiorTensor d.grading d.representation_graded)

private def tensorComparisonGradingCoefficientEquiv :=
  tensorCoefficientExtensionEquiv (E := E) β γ d.groupAction
    d.representation d.representation_equivariant

private def tensorComparisonGradingAssociator :=
  InteriorModuleTensorAssociator.hilbertEquiv
    (B := B) (C := C) (D := ReducedCrossedProduct γ)
    (E := E) (F := F) (G := (ReducedCrossedProduct γ)ᵐᵒᵖ)
    d.representation (coefficientRepresentation γ)

private def tensorComparisonGradingCoefficientCLM :=
  (tensorComparisonGradingCoefficientEquiv (E := E) β γ d).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap

private def tensorComparisonGradingSourceCLM :=
  (tensorComparisonGradingSource β γ J d).grading.toContinuousLinearEquiv.toContinuousLinearMap

private def tensorComparisonGradingMiddleCLM :
    tensorComparisonGradingMiddleCarrier (E := E) β γ d →L[ℂ]
      tensorComparisonGradingMiddleCarrier (E := E) β γ d :=
  (tensorComparisonGradingMiddle β γ J d).grading.toContinuousLinearEquiv.toContinuousLinearMap

private def tensorComparisonGradingPureFirstCLM (z : Module γ F) :=
  InteriorModuleTensorScalarExtension.pureCLM
    (B := ReducedCrossedProduct β) (C := ReducedCrossedProduct γ)
    (E := Module β E) (H := Module γ F) (tensorComparisonGradingRho β γ d) z

private theorem tensorComparisonGradingSource_mk (ξ : Module β E) (z : Module γ F) :
    (tensorComparisonGradingSource β γ J d).grading
        (interiorModuleTensorMk (E := Module β E) (tensorComparisonGradingRho β γ d) ξ z) =
      interiorModuleTensorMk (E := Module β E) (tensorComparisonGradingRho β γ d)
        ((tensorComparisonGradingJB β γ J d).grading ξ)
        ((tensorComparisonGradingK β γ d).grading z) :=
  GradedHilbertModule.interiorTensor_grading_mk
    (B := ReducedCrossedProduct β) (C := ReducedCrossedProduct γ)
    (E := Module β E) (F := Module γ F) (φ := tensorComparisonGradingRho β γ d)
    (tensorComparisonGradingJB β γ J d) (tensorComparisonGradingK β γ d)
    (tensorComparisonGradingRho_graded β γ d) ξ z

private theorem tensorComparisonGradingJB_mk
    (x : E) (a : (ReducedCrossedProduct β)ᵐᵒᵖ) :
    (tensorComparisonGradingJB β γ J d).grading (mk β E x a) =
      mk β E (J.grading x)
        (MulOpposite.op
          ((reducedCrossedProductGrading β δB d.sourceAction_preservesGrading).automorphism
            (MulOpposite.unop a))) :=
  moduleGrading_mk (Γ := Γ) (B := B) (E := E)
    β δB d.sourceAction_preservesGrading J x a

private def tensorComparisonGradingMiddleMk
    (x : E) (z : InteriorModuleTensor (E := F) (coefficientRepresentation γ)) :
    tensorComparisonGradingMiddleCarrier (E := E) β γ d :=
  interiorModuleTensorMk
    (B := B) (C := ReducedCrossedProduct γ) (E := E)
    (F := InteriorModuleTensor (E := F) (coefficientRepresentation γ))
    (InteriorModuleTensorAssociator.rightRepresentation d.representation
      (coefficientRepresentation γ)) x z

private theorem tensorComparisonGradingMiddle_mk
    (x : E) (z : InteriorModuleTensor (E := F) (coefficientRepresentation γ)) :
    (tensorComparisonGradingMiddle β γ J d).grading
        (tensorComparisonGradingMiddleMk (E := E) β γ d x z) =
      tensorComparisonGradingMiddleMk (E := E) β γ d
        (J.grading x) ((tensorComparisonGradingK β γ d).grading z) :=
  GradedHilbertModule.interiorTensor_grading_mk
    (B := B) (C := ReducedCrossedProduct γ) (E := E)
    (F := InteriorModuleTensor (E := F) (coefficientRepresentation γ))
    (φ := InteriorModuleTensorAssociator.rightRepresentation d.representation
      (coefficientRepresentation γ))
    J (tensorComparisonGradingK β γ d) (tensorComparisonGradingPsi_graded β γ d) x z

private theorem tensorComparisonGrading_factor
    (v : InteriorModuleTensor (E := Module β E) (tensorComparisonGradingRho β γ d)) :
    tensorComparisonGradingAssociator (E := E) β γ d
        (tensorComparison β γ d.groupAction d.representation d.representation_equivariant v) =
      tensorComparisonGradingCoefficientEquiv (E := E) β γ d v :=
  (tensorComparisonGradingAssociator (E := E) β γ d).apply_symm_apply
    (tensorComparisonGradingCoefficientEquiv (E := E) β γ d v)

private theorem tensorComparisonGrading_associator
    (v : Module γ (InteriorModuleTensor (E := E) d.representation)) :
    tensorComparisonGradingAssociator (E := E) β γ d
        ((tensorComparisonGradingTarget β γ J d).grading v) =
      (tensorComparisonGradingMiddle β γ J d).grading
        (tensorComparisonGradingAssociator (E := E) β γ d v) :=
  InteriorModuleTensorAssociator.hilbertEquiv_grading_intertwine
    (B := B) (C := C) (D := ReducedCrossedProduct γ)
    (E := E) (F := F) (G := (ReducedCrossedProduct γ)ᵐᵒᵖ)
    d.representation (coefficientRepresentation γ) J d.grading
    (crossedStandardGrading γ δC d.coefficientAction_preservesGrading)
    d.representation_graded
    (coefficientRepresentation_graded γ δC d.coefficientAction_preservesGrading) v

private theorem tensorComparison_coefficient_grading_mk_aux
    (x : E) (a : (ReducedCrossedProduct β)ᵐᵒᵖ) (z : Module γ F) :
    tensorComparisonGradingCoefficientEquiv (E := E) β γ d
        ((tensorComparisonGradingSource β γ J d).grading
          (interiorModuleTensorMk (E := Module β E)
            (tensorComparisonGradingRho β γ d) (mk β E x a) z)) =
      (tensorComparisonGradingMiddle β γ J d).grading
        (tensorComparisonGradingCoefficientEquiv (E := E) β γ d
          (interiorModuleTensorMk (E := Module β E)
            (tensorComparisonGradingRho β γ d) (mk β E x a) z)) := by
  let ρ := tensorComparisonGradingRho β γ d
  let DB := reducedCrossedProductGrading β δB d.sourceAction_preservesGrading
  let K := tensorComparisonGradingK β γ d
  let JB := tensorComparisonGradingJB β γ J d
  let JS := tensorComparisonGradingSource β γ J d
  let JT := tensorComparisonGradingMiddle β γ J d
  let e := tensorComparisonGradingCoefficientEquiv (E := E) β γ d
  let m := tensorComparisonGradingMiddleMk (E := E) β γ d
  calc
    e (JS.grading (interiorModuleTensorMk ρ (mk β E x a) z)) =
        e (interiorModuleTensorMk ρ (JB.grading (mk β E x a)) (K.grading z)) :=
      congrArg (fun w : InteriorModuleTensor (E := Module β E) ρ => e w)
        (tensorComparisonGradingSource_mk β γ J d (mk β E x a) z)
    _ = e (interiorModuleTensorMk ρ
        (mk β E (J.grading x) (MulOpposite.op (DB.automorphism (MulOpposite.unop a))))
        (K.grading z)) :=
      congrArg (fun v : Module β E => e (interiorModuleTensorMk ρ v (K.grading z)))
        (tensorComparisonGradingJB_mk β γ J d x a)
    _ = m (J.grading x)
        (ρ (DB.automorphism (MulOpposite.unop a)) (K.grading z)) :=
      tensorComparison_coefficient_mk_aux (Γ := Γ) (B := B) (C := C)
        (E := E) (F := F) β γ d (J.grading x)
        (MulOpposite.op (DB.automorphism (MulOpposite.unop a))) (K.grading z)
    _ = m (J.grading x)
        (K.grading (ρ (MulOpposite.unop a) z)) :=
      congrArg (fun w : InteriorModuleTensor (E := F) (coefficientRepresentation γ) => m (J.grading x) w)
        (tensorComparisonGradingRho_graded β γ d (MulOpposite.unop a) z).symm
    _ = JT.grading (m x (ρ (MulOpposite.unop a) z)) :=
      (tensorComparisonGradingMiddle_mk β γ J d x (ρ (MulOpposite.unop a) z)).symm
    _ = JT.grading (e (interiorModuleTensorMk ρ (mk β E x a) z)) :=
      congrArg (fun w : tensorComparisonGradingMiddleCarrier (E := E) β γ d => JT.grading w)
        (tensorComparison_coefficient_mk_aux (Γ := Γ) (B := B) (C := C)
          (E := E) (F := F) β γ d x a z).symm

private theorem tensorComparison_coefficient_grading_first_clm_aux (z : Module γ F) :
    ((tensorComparisonGradingCoefficientCLM (E := E) β γ d).comp
        (tensorComparisonGradingSourceCLM β γ J d)).comp
        (tensorComparisonGradingPureFirstCLM (E := E) β γ d z) =
      ((tensorComparisonGradingMiddleCLM β γ J d).comp
        (tensorComparisonGradingCoefficientCLM (E := E) β γ d)).comp
        (tensorComparisonGradingPureFirstCLM (E := E) β γ d z) := by
  apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    (B := B) (C := ReducedCrossedProduct β)
    (E := E) (F := (ReducedCrossedProduct β)ᵐᵒᵖ)
    (φ := coefficientRepresentation β)
  intro x a
  exact tensorComparison_coefficient_grading_mk_aux
    (Γ := Γ) (B := B) (C := C) (E := E) (F := F) β γ J d x a z

private theorem tensorComparison_coefficient_grading_clm_aux :
    (tensorComparisonGradingCoefficientCLM (E := E) β γ d).comp
        (tensorComparisonGradingSourceCLM β γ J d) =
      (tensorComparisonGradingMiddleCLM β γ J d).comp
        (tensorComparisonGradingCoefficientCLM (E := E) β γ d) := by
  apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    (B := ReducedCrossedProduct β) (C := ReducedCrossedProduct γ)
    (E := Module β E) (F := Module γ F) (φ := tensorComparisonGradingRho β γ d)
  intro ξ z
  exact DFunLike.congr_fun
    (tensorComparison_coefficient_grading_first_clm_aux
      (Γ := Γ) (B := B) (C := C) (E := E) (F := F) β γ J d z) ξ

private theorem tensorComparison_coefficient_grading_aux
    (u : InteriorModuleTensor (E := Module β E) (tensorComparisonGradingRho β γ d)) :
    tensorComparisonGradingCoefficientEquiv (E := E) β γ d
        ((tensorComparisonGradingSource β γ J d).grading u) =
      (tensorComparisonGradingMiddle β γ J d).grading
        (tensorComparisonGradingCoefficientEquiv (E := E) β γ d u) :=
  DFunLike.congr_fun
    (tensorComparison_coefficient_grading_clm_aux
      (Γ := Γ) (B := B) (C := C) (E := E) (F := F) β γ J d) u

/-- The entire actual crossed tensor unitary preserves the genuine module
grading. No assumption that this comparison is even is used. -/
theorem tensorComparison_grading
    (u : InteriorModuleTensor (E := Module β E)
      (reducedSourceRepresentation γ F β d.groupAction d.representation d.representation_equivariant)) :
    tensorComparison β γ d.groupAction d.representation d.representation_equivariant
      (((moduleGrading β δB d.sourceAction_preservesGrading J).interiorTensor
        (moduleGrading γ δC d.coefficientAction_preservesGrading d.grading)
        (fun z v => reducedSourceRepresentation_graded γ β d z v)).grading u) =
      (moduleGrading γ δC d.coefficientAction_preservesGrading
        (J.interiorTensor d.grading d.representation_graded)).grading
          (tensorComparison β γ d.groupAction d.representation d.representation_equivariant u) := by
  apply (tensorComparisonGradingAssociator (E := E) β γ d).injective
  calc
    tensorComparisonGradingAssociator (E := E) β γ d
        (tensorComparison β γ d.groupAction d.representation d.representation_equivariant
          ((tensorComparisonGradingSource β γ J d).grading u)) =
        tensorComparisonGradingCoefficientEquiv (E := E) β γ d
          ((tensorComparisonGradingSource β γ J d).grading u) :=
      tensorComparisonGrading_factor (E := E) β γ d
        ((tensorComparisonGradingSource β γ J d).grading u)
    _ = (tensorComparisonGradingMiddle β γ J d).grading
        (tensorComparisonGradingCoefficientEquiv (E := E) β γ d u) :=
      tensorComparison_coefficient_grading_aux
        (Γ := Γ) (B := B) (C := C) (E := E) (F := F) β γ J d u
    _ = (tensorComparisonGradingMiddle β γ J d).grading
        (tensorComparisonGradingAssociator (E := E) β γ d
          (tensorComparison β γ d.groupAction d.representation d.representation_equivariant u)) :=
      congrArg
        (fun w : InteriorModuleTensor (E := E) (tensorComparisonGradingPsi β γ d) =>
          (tensorComparisonGradingMiddle β γ J d).grading w)
        (tensorComparisonGrading_factor (E := E) β γ d u).symm
    _ = tensorComparisonGradingAssociator (E := E) β γ d
        ((tensorComparisonGradingTarget β γ J d).grading
          (tensorComparison β γ d.groupAction d.representation d.representation_equivariant u)) :=
      (tensorComparisonGrading_associator β γ J d
        (tensorComparison β γ d.groupAction d.representation d.representation_equivariant u)).symm

end BC4lean.KKTheory.KasparovDescent
