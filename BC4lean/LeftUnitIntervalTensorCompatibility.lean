import BC4lean.LeftUnitIntervalTensor

/-! # Whole-module compatibility of the left-unit endpoint maps

The endpoint identifications intertwine the actual module grading, group
action and left A representation. Identities are proved first on pure tensors,
then on the entire completed tensor, then on the entire intrinsic fibre.
No operator or connection endpoint compatibility is presumed in these maps.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {Γ A B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

/- Cache the original separated/completed structures while elaborating endpoint statements. -/
local instance leftUnitCompatibilityPreTensorCStarModule
  {A B E : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  (φ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) :
    CStarModule C(unitInterval, B)ᵐᵒᵖ
      (PreHilbertModuleTensor (E := LeftUnitIntervalIdeal A)
        (leftUnitIntervalSectionRepresentation φ)) :=
  preModuleTensorCStarModule (E := LeftUnitIntervalIdeal A)
    (leftUnitIntervalSectionRepresentation φ)

local instance leftUnitCompatibilityTensorCStarModule
  {A B E : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  (φ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) :
    CStarModule C(unitInterval, B)ᵐᵒᵖ (LeftUnitIntervalTensor φ) :=
  completionCStarModule (B := C(unitInterval, B))
    (E := PreHilbertModuleTensor (E := LeftUnitIntervalIdeal A)
      (leftUnitIntervalSectionRepresentation φ))

local instance leftUnitCompatibilityOnePreTensorCStarModule
  {A B E : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  (φ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) :
    CStarModule Bᵐᵒᵖ (PreHilbertModuleTensor (E := Aᵐᵒᵖ) φ) :=
  preModuleTensorCStarModule (E := Aᵐᵒᵖ) φ

local instance leftUnitCompatibilityOneTensorCStarModule
  {A B E : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  (φ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) :
    CStarModule Bᵐᵒᵖ (InteriorModuleTensor (E := Aᵐᵒᵖ) φ) :=
  completionCStarModule (B := B)
    (E := PreHilbertModuleTensor (E := Aᵐᵒᵖ) φ)

namespace GradedKasparovCycle
variable (c : GradedKasparovCycle α β δA δB E)

def leftUnitTensorGrading : GradedHilbertModule (δB.continuousSections (X := unitInterval))
    (LeftUnitIntervalTensor c.representation) :=
  (leftUnitIntervalGrading δA).interiorTensor (c.grading.gradedContinuousSections (X := unitInterval))
    c.leftUnitIntervalSecondRepresentation_graded

def leftUnitTensorAction : EquivariantHilbertModule (β.continuousSections (X := unitInterval))
    (LeftUnitIntervalTensor c.representation) :=
  (leftUnitIntervalAction α).interiorTensor (c.groupAction.continuousSections (X := unitInterval))
    c.leftUnitIntervalSecondRepresentation_equivariant

theorem leftUnitTensorAction_preservesGrading :
    c.leftUnitTensorAction.PreservesGrading c.leftUnitTensorGrading := by
  have hE : (c.groupAction.continuousSections (X := unitInterval)).PreservesGrading
      (c.grading.gradedContinuousSections (X := unitInterval)) := by
    intro g s
    apply ContinuousMap.ext
    intro t
    exact c.grading_preserved g (s t)
  exact EquivariantHilbertModule.interiorTensor_preservesGrading
    (leftUnitIntervalAction α) (c.groupAction.continuousSections (X := unitInterval))
    (leftUnitIntervalGrading δA) (c.grading.gradedContinuousSections (X := unitInterval))
    (leftUnitIntervalAction_preservesGrading c.sourceAction_preservesGrading) hE
    c.leftUnitIntervalSecondRepresentation_equivariant c.leftUnitIntervalSecondRepresentation_graded

def leftUnitTensorRepresentation : A →⋆ₙₐ[ℂ]
    AdjointableMap C(unitInterval, B) (LeftUnitIntervalTensor c.representation)
      (LeftUnitIntervalTensor c.representation) :=
  (interiorModuleTensorOperatorHom (leftUnitIntervalSectionRepresentation c.representation)).toNonUnitalStarAlgHom.comp
    leftUnitIntervalRepresentation

set_option maxHeartbeats 2400000 in
theorem leftUnitTensorRepresentation_graded (a : A) (u : LeftUnitIntervalTensor c.representation) :
    c.leftUnitTensorGrading.grading (c.leftUnitTensorRepresentation a u) =
      c.leftUnitTensorRepresentation (δA.automorphism a) (c.leftUnitTensorGrading.grading u) := by
  have hφ : ModuleTensorRepresentationGraded
      (δB := δA.leftUnitUnitization.continuousSections (X := unitInterval))
      (leftUnitIntervalSectionRepresentation c.representation)
      (c.grading.gradedContinuousSections (X := unitInterval)) :=
    c.leftUnitIntervalSecondRepresentation_graded
  have h : c.leftUnitTensorGrading.grading.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (c.leftUnitTensorRepresentation a).toCLM =
      (c.leftUnitTensorRepresentation (δA.automorphism a)).toCLM.comp
        c.leftUnitTensorGrading.grading.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro j s
    change ((leftUnitIntervalGrading δA).interiorTensor
      (c.grading.gradedContinuousSections (X := unitInterval))
      hφ).grading
        (interiorModuleTensorOperator (leftUnitIntervalSectionRepresentation c.representation)
          (leftUnitIntervalRepresentation a)
          (interiorModuleTensorMk (leftUnitIntervalSectionRepresentation c.representation) j s)) =
      interiorModuleTensorOperator (leftUnitIntervalSectionRepresentation c.representation)
        (leftUnitIntervalRepresentation (δA.automorphism a))
        (((leftUnitIntervalGrading δA).interiorTensor
          (c.grading.gradedContinuousSections (X := unitInterval))
          hφ).grading
            (interiorModuleTensorMk (leftUnitIntervalSectionRepresentation c.representation) j s))
    rw [interiorModuleTensorOperator_mk
      (leftUnitIntervalSectionRepresentation c.representation)
      (leftUnitIntervalRepresentation a) j s]
    rw [GradedHilbertModule.interiorTensor_grading_mk
      (φ := leftUnitIntervalSectionRepresentation c.representation)
      (leftUnitIntervalGrading δA) (c.grading.gradedContinuousSections (X := unitInterval))
      hφ (leftUnitIntervalRepresentation a j) s]
    rw [GradedHilbertModule.interiorTensor_grading_mk
      (φ := leftUnitIntervalSectionRepresentation c.representation)
      (leftUnitIntervalGrading δA) (c.grading.gradedContinuousSections (X := unitInterval))
      hφ j s]
    rw [interiorModuleTensorOperator_mk
      (leftUnitIntervalSectionRepresentation c.representation)
      (leftUnitIntervalRepresentation (δA.automorphism a))
      ((leftUnitIntervalGrading δA).grading j)
      ((c.grading.gradedContinuousSections (X := unitInterval)).grading s)]
    exact congrArg
      (fun z : LeftUnitIntervalIdeal A =>
        interiorModuleTensorMk (E := LeftUnitIntervalIdeal A)
          (leftUnitIntervalSectionRepresentation c.representation) z
          ((c.grading.gradedContinuousSections (X := unitInterval)).grading s))
      (leftUnitIntervalRepresentation_graded δA a j)
  exact DFunLike.congr_fun h u

theorem leftUnitTensorRepresentation_equivariant (g : Γ) (a : A) :
    c.leftUnitTensorAction.conjugateOperator g (c.leftUnitTensorRepresentation a) =
      c.leftUnitTensorRepresentation (α.automorphism g a) := by
  change ((leftUnitIntervalAction α).interiorTensor (c.groupAction.continuousSections (X := unitInterval))
      c.leftUnitIntervalSecondRepresentation_equivariant).conjugateOperator g
        (interiorModuleTensorOperator (leftUnitIntervalSectionRepresentation c.representation)
          (leftUnitIntervalRepresentation a)) = _
  rw [EquivariantHilbertModule.interiorTensor_conjugateOperator,
    leftUnitIntervalRepresentation_equivariant]
  rfl

def leftUnitOneEndpointGrading :
    GradedHilbertModule δB (InteriorModuleTensor (E := Aᵐᵒᵖ) c.representation) :=
  (GradedHilbertModule.standard δA).interiorTensor c.grading c.representation_graded

def leftUnitOneEndpointAction :
    EquivariantHilbertModule β (InteriorModuleTensor (E := Aᵐᵒᵖ) c.representation) :=
  (EquivariantHilbertModule.standard α).interiorTensor c.groupAction
    (EquivariantHilbertModule.representationEquivariant_of_conjugate c.groupAction
      c.representation_equivariant)

def leftUnitOneEndpointRepresentation : A →⋆ₙₐ[ℂ]
    AdjointableMap B (InteriorModuleTensor (E := Aᵐᵒᵖ) c.representation)
      (InteriorModuleTensor (E := Aᵐᵒᵖ) c.representation) :=
  (interiorModuleTensorOperatorHom c.representation).toNonUnitalStarAlgHom.comp standardLeftMul

set_option maxHeartbeats 600000 in
theorem leftUnitZeroEvaluation_grading (u : LeftUnitIntervalTensor c.representation) :
    LeftUnitIntervalTensor.zeroEvaluation c.representation (c.leftUnitTensorGrading.grading u) =
      c.grading.grading (LeftUnitIntervalTensor.zeroEvaluation c.representation u) := by
  have h : (LeftUnitIntervalTensor.zeroEvaluation c.representation).comp
      c.leftUnitTensorGrading.grading.toContinuousLinearEquiv.toContinuousLinearMap =
      c.grading.grading.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (LeftUnitIntervalTensor.zeroEvaluation c.representation) := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro j s
    change LeftUnitIntervalTensor.zeroEvaluation c.representation
      (((leftUnitIntervalGrading δA).interiorTensor
        (c.grading.gradedContinuousSections (X := unitInterval))
        c.leftUnitIntervalSecondRepresentation_graded).grading
          (interiorModuleTensorMk (leftUnitIntervalSectionRepresentation c.representation) j s)) =
      c.grading.grading (LeftUnitIntervalTensor.zeroEvaluation c.representation
        (interiorModuleTensorMk (leftUnitIntervalSectionRepresentation c.representation) j s))
    rw [GradedHilbertModule.interiorTensor_grading_mk,
      LeftUnitIntervalTensor.zeroEvaluation_mk, LeftUnitIntervalTensor.zeroEvaluation_mk]
    change leftUnitExtendedRepresentation c.representation
      (δA.leftUnitUnitization.automorphism
        (MulOpposite.unop (j : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) (0 : unitInterval)))
      (c.grading.grading (s (0 : unitInterval))) = _
    exact (c.leftUnitExtendedRepresentation_graded _ (s 0)).symm
  exact DFunLike.congr_fun h u

set_option maxHeartbeats 600000 in
theorem leftUnitOneEvaluation_grading (u : LeftUnitIntervalTensor c.representation) :
    LeftUnitIntervalTensor.oneEvaluation c.representation (c.leftUnitTensorGrading.grading u) =
      c.leftUnitOneEndpointGrading.grading (LeftUnitIntervalTensor.oneEvaluation c.representation u) := by
  have hφ : ModuleTensorRepresentationGraded
      (δB := δA.leftUnitUnitization.continuousSections (X := unitInterval))
      (leftUnitIntervalSectionRepresentation c.representation)
      (c.grading.gradedContinuousSections (X := unitInterval)) :=
    c.leftUnitIntervalSecondRepresentation_graded
  have hφ₁ : ModuleTensorRepresentationGraded (δB := δA) c.representation c.grading :=
    c.representation_graded
  have h : (LeftUnitIntervalTensor.oneEvaluation c.representation).comp
      c.leftUnitTensorGrading.grading.toContinuousLinearEquiv.toContinuousLinearMap =
      c.leftUnitOneEndpointGrading.grading.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (LeftUnitIntervalTensor.oneEvaluation c.representation) := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro j s
    change LeftUnitIntervalTensor.oneEvaluation c.representation
      (((leftUnitIntervalGrading δA).interiorTensor
        (c.grading.gradedContinuousSections (X := unitInterval))
        hφ).grading
          (interiorModuleTensorMk (leftUnitIntervalSectionRepresentation c.representation) j s)) =
      ((GradedHilbertModule.standard δA).interiorTensor c.grading hφ₁).grading
        (LeftUnitIntervalTensor.oneEvaluation c.representation
          (interiorModuleTensorMk (leftUnitIntervalSectionRepresentation c.representation) j s))
    rw [GradedHilbertModule.interiorTensor_grading_mk
      (φ := leftUnitIntervalSectionRepresentation c.representation)
      (leftUnitIntervalGrading δA) (c.grading.gradedContinuousSections (X := unitInterval))
      hφ j s]
    rw [LeftUnitIntervalTensor.oneEvaluation_mk, LeftUnitIntervalTensor.oneEvaluation_mk]
    exact (GradedHilbertModule.interiorTensor_grading_mk (φ := c.representation)
      (GradedHilbertModule.standard δA) c.grading hφ₁
      (LeftUnitIntervalTensor.oneCoefficient j) (s 1)).symm
  exact DFunLike.congr_fun h u

set_option maxHeartbeats 600000 in
theorem leftUnitZeroEvaluation_action (g : Γ) (u : LeftUnitIntervalTensor c.representation) :
    LeftUnitIntervalTensor.zeroEvaluation c.representation (c.leftUnitTensorAction.action g u) =
      c.groupAction.action g (LeftUnitIntervalTensor.zeroEvaluation c.representation u) := by
  have hφ := EquivariantHilbertModule.representationEquivariant_of_conjugate
    (φ := (leftUnitExtendedRepresentation c.representation).toNonUnitalStarAlgHom)
    c.groupAction c.leftUnitExtendedRepresentation_equivariant
  have h : (LeftUnitIntervalTensor.zeroEvaluation c.representation).comp
      (c.leftUnitTensorAction.action g).toContinuousLinearEquiv.toContinuousLinearMap =
      (c.groupAction.action g).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (LeftUnitIntervalTensor.zeroEvaluation c.representation) := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro j s
    change LeftUnitIntervalTensor.zeroEvaluation c.representation
      ((((leftUnitIntervalAction α).interiorTensor
        (c.groupAction.continuousSections (X := unitInterval))
        c.leftUnitIntervalSecondRepresentation_equivariant).action g)
          (interiorModuleTensorMk (leftUnitIntervalSectionRepresentation c.representation) j s)) =
      c.groupAction.action g (LeftUnitIntervalTensor.zeroEvaluation c.representation
        (interiorModuleTensorMk (leftUnitIntervalSectionRepresentation c.representation) j s))
    rw [EquivariantHilbertModule.interiorTensor_action_mk,
      LeftUnitIntervalTensor.zeroEvaluation_mk, LeftUnitIntervalTensor.zeroEvaluation_mk]
    change leftUnitExtendedRepresentation c.representation
      (α.leftUnitUnitization.automorphism g
        (MulOpposite.unop (j : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) (0 : unitInterval)))
      (c.groupAction.action g (s (0 : unitInterval))) = _
    exact (hφ g _ (s 0)).symm
  exact DFunLike.congr_fun h u

set_option maxHeartbeats 600000 in
theorem leftUnitOneEvaluation_action (g : Γ) (u : LeftUnitIntervalTensor c.representation) :
    LeftUnitIntervalTensor.oneEvaluation c.representation (c.leftUnitTensorAction.action g u) =
      c.leftUnitOneEndpointAction.action g (LeftUnitIntervalTensor.oneEvaluation c.representation u) := by
  have h : (LeftUnitIntervalTensor.oneEvaluation c.representation).comp
      (c.leftUnitTensorAction.action g).toContinuousLinearEquiv.toContinuousLinearMap =
      (c.leftUnitOneEndpointAction.action g).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (LeftUnitIntervalTensor.oneEvaluation c.representation) := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro j s
    change LeftUnitIntervalTensor.oneEvaluation c.representation
      ((((leftUnitIntervalAction α).interiorTensor
        (c.groupAction.continuousSections (X := unitInterval))
        c.leftUnitIntervalSecondRepresentation_equivariant).action g)
          (interiorModuleTensorMk (leftUnitIntervalSectionRepresentation c.representation) j s)) =
      (((EquivariantHilbertModule.standard α).interiorTensor c.groupAction
        (EquivariantHilbertModule.representationEquivariant_of_conjugate c.groupAction
          c.representation_equivariant)).action g)
        (LeftUnitIntervalTensor.oneEvaluation c.representation
          (interiorModuleTensorMk (leftUnitIntervalSectionRepresentation c.representation) j s))
    rw [EquivariantHilbertModule.interiorTensor_action_mk,
      LeftUnitIntervalTensor.oneEvaluation_mk, LeftUnitIntervalTensor.oneEvaluation_mk,
      EquivariantHilbertModule.interiorTensor_action_mk]
    rfl
  exact DFunLike.congr_fun h u

set_option maxHeartbeats 600000 in
theorem leftUnitZeroEvaluation_representation (a : A) (u : LeftUnitIntervalTensor c.representation) :
    LeftUnitIntervalTensor.zeroEvaluation c.representation (c.leftUnitTensorRepresentation a u) =
      c.representation a (LeftUnitIntervalTensor.zeroEvaluation c.representation u) := by
  have h : (LeftUnitIntervalTensor.zeroEvaluation c.representation).comp
      (c.leftUnitTensorRepresentation a).toCLM =
      (c.representation a).toCLM.comp (LeftUnitIntervalTensor.zeroEvaluation c.representation) := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro j s
    change LeftUnitIntervalTensor.zeroEvaluation c.representation
      (interiorModuleTensorOperator (leftUnitIntervalSectionRepresentation c.representation)
        (leftUnitIntervalRepresentation a)
        (interiorModuleTensorMk (leftUnitIntervalSectionRepresentation c.representation) j s)) =
      c.representation a (LeftUnitIntervalTensor.zeroEvaluation c.representation
        (interiorModuleTensorMk (leftUnitIntervalSectionRepresentation c.representation) j s))
    rw [interiorModuleTensorOperator_mk,
      LeftUnitIntervalTensor.zeroEvaluation_mk, LeftUnitIntervalTensor.zeroEvaluation_mk]
    change leftUnitExtendedRepresentation c.representation
      ((a : Unitization ℂ A) *
        MulOpposite.unop (j : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) (0 : unitInterval))
      (s (0 : unitInterval)) = _
    rw [map_mul, leftUnitExtendedRepresentation_inr, AdjointableMap.mul_apply]
  exact DFunLike.congr_fun h u

set_option maxHeartbeats 600000 in
theorem leftUnitOneEvaluation_representation (a : A) (u : LeftUnitIntervalTensor c.representation) :
    LeftUnitIntervalTensor.oneEvaluation c.representation (c.leftUnitTensorRepresentation a u) =
      c.leftUnitOneEndpointRepresentation a (LeftUnitIntervalTensor.oneEvaluation c.representation u) := by
  have h : (LeftUnitIntervalTensor.oneEvaluation c.representation).comp
      (c.leftUnitTensorRepresentation a).toCLM =
      (c.leftUnitOneEndpointRepresentation a).toCLM.comp (LeftUnitIntervalTensor.oneEvaluation c.representation) := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro j s
    change LeftUnitIntervalTensor.oneEvaluation c.representation
      (interiorModuleTensorOperator (leftUnitIntervalSectionRepresentation c.representation)
        (leftUnitIntervalRepresentation a)
        (interiorModuleTensorMk (leftUnitIntervalSectionRepresentation c.representation) j s)) =
      interiorModuleTensorOperator c.representation (standardLeftMul a)
        (LeftUnitIntervalTensor.oneEvaluation c.representation
          (interiorModuleTensorMk (leftUnitIntervalSectionRepresentation c.representation) j s))
    rw [interiorModuleTensorOperator_mk,
      LeftUnitIntervalTensor.oneEvaluation_mk, LeftUnitIntervalTensor.oneEvaluation_mk,
      interiorModuleTensorOperator_mk]
    apply congrArg (fun x : Aᵐᵒᵖ => interiorModuleTensorMk c.representation x (s 1))
    apply MulOpposite.unop_injective
    change ((a : Unitization ℂ A) *
      MulOpposite.unop (j : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 1).snd =
      a * (MulOpposite.unop (j : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 1).snd
    rw [Unitization.snd_mul, Unitization.fst_inr, Unitization.snd_inr,
      leftUnitIntervalIdeal_scalar_one, zero_smul, zero_smul, zero_add, zero_add]
  exact DFunLike.congr_fun h u

set_option maxHeartbeats 600000 in
theorem leftUnitZeroFibreEquiv_grading (z : HilbertModuleFibre (X := unitInterval) B (LeftUnitIntervalTensor c.representation) (0 : unitInterval)) :
    LeftUnitIntervalTensor.zeroFibreEquiv c.representation ((c.leftUnitTensorGrading.gradedFibre (0 : unitInterval)).grading z) =
      c.grading.grading (LeftUnitIntervalTensor.zeroFibreEquiv c.representation z) := by
  obtain ⟨u, rfl⟩ := hilbertModuleFibreMk_surjective (X := unitInterval) (B := B)
    (M := LeftUnitIntervalTensor c.representation) (0 : unitInterval) z
  rw [GradedHilbertModule.gradedFibre_grading_mk, LeftUnitIntervalTensor.zeroFibreEquiv_mk,
    LeftUnitIntervalTensor.zeroFibreEquiv_mk, c.leftUnitZeroEvaluation_grading]

set_option maxHeartbeats 600000 in
theorem leftUnitOneFibreEquiv_grading (z : HilbertModuleFibre (X := unitInterval) B (LeftUnitIntervalTensor c.representation) (1 : unitInterval)) :
    LeftUnitIntervalTensor.oneFibreEquiv c.representation ((c.leftUnitTensorGrading.gradedFibre (1 : unitInterval)).grading z) =
      c.leftUnitOneEndpointGrading.grading (LeftUnitIntervalTensor.oneFibreEquiv c.representation z) := by
  obtain ⟨u, rfl⟩ := hilbertModuleFibreMk_surjective (X := unitInterval) (B := B)
    (M := LeftUnitIntervalTensor c.representation) (1 : unitInterval) z
  rw [GradedHilbertModule.gradedFibre_grading_mk, LeftUnitIntervalTensor.oneFibreEquiv_mk,
    LeftUnitIntervalTensor.oneFibreEquiv_mk, c.leftUnitOneEvaluation_grading]

set_option maxHeartbeats 1200000 in
theorem leftUnitZeroFibreEquiv_action (g : Γ)
    (z : HilbertModuleFibre (X := unitInterval) B (LeftUnitIntervalTensor c.representation) (0 : unitInterval)) :
    LeftUnitIntervalTensor.zeroFibreEquiv c.representation ((c.leftUnitTensorAction.fibre (0 : unitInterval)).action g z) =
      c.groupAction.action g (LeftUnitIntervalTensor.zeroFibreEquiv c.representation z) := by
  obtain ⟨u, rfl⟩ := hilbertModuleFibreMk_surjective (X := unitInterval) (B := B)
    (M := LeftUnitIntervalTensor c.representation) (0 : unitInterval) z
  rw [EquivariantHilbertModule.fibre_action_mk, LeftUnitIntervalTensor.zeroFibreEquiv_mk,
    LeftUnitIntervalTensor.zeroFibreEquiv_mk, c.leftUnitZeroEvaluation_action]

set_option maxHeartbeats 1200000 in
theorem leftUnitOneFibreEquiv_action (g : Γ)
    (z : HilbertModuleFibre (X := unitInterval) B (LeftUnitIntervalTensor c.representation) (1 : unitInterval)) :
    LeftUnitIntervalTensor.oneFibreEquiv c.representation ((c.leftUnitTensorAction.fibre (1 : unitInterval)).action g z) =
      c.leftUnitOneEndpointAction.action g (LeftUnitIntervalTensor.oneFibreEquiv c.representation z) := by
  obtain ⟨u, rfl⟩ := hilbertModuleFibreMk_surjective (X := unitInterval) (B := B)
    (M := LeftUnitIntervalTensor c.representation) (1 : unitInterval) z
  rw [EquivariantHilbertModule.fibre_action_mk, LeftUnitIntervalTensor.oneFibreEquiv_mk,
    LeftUnitIntervalTensor.oneFibreEquiv_mk, c.leftUnitOneEvaluation_action]

set_option maxHeartbeats 600000 in
theorem leftUnitZeroFibreEquiv_representation (a : A)
    (z : HilbertModuleFibre (X := unitInterval) B (LeftUnitIntervalTensor c.representation) (0 : unitInterval)) :
    LeftUnitIntervalTensor.zeroFibreEquiv c.representation
      (hilbertModuleFibreOperator (X := unitInterval) (B := B) (0 : unitInterval) (c.leftUnitTensorRepresentation a) z) =
      c.representation a (LeftUnitIntervalTensor.zeroFibreEquiv c.representation z) := by
  obtain ⟨u, rfl⟩ := hilbertModuleFibreMk_surjective (X := unitInterval) (B := B)
    (M := LeftUnitIntervalTensor c.representation) (0 : unitInterval) z
  rw [hilbertModuleFibreOperator_mk, LeftUnitIntervalTensor.zeroFibreEquiv_mk,
    LeftUnitIntervalTensor.zeroFibreEquiv_mk, c.leftUnitZeroEvaluation_representation]

set_option maxHeartbeats 600000 in
theorem leftUnitOneFibreEquiv_representation (a : A)
    (z : HilbertModuleFibre (X := unitInterval) B (LeftUnitIntervalTensor c.representation) (1 : unitInterval)) :
    LeftUnitIntervalTensor.oneFibreEquiv c.representation
      (hilbertModuleFibreOperator (X := unitInterval) (B := B) (1 : unitInterval) (c.leftUnitTensorRepresentation a) z) =
      c.leftUnitOneEndpointRepresentation a (LeftUnitIntervalTensor.oneFibreEquiv c.representation z) := by
  obtain ⟨u, rfl⟩ := hilbertModuleFibreMk_surjective (X := unitInterval) (B := B)
    (M := LeftUnitIntervalTensor c.representation) (1 : unitInterval) z
  rw [hilbertModuleFibreOperator_mk, LeftUnitIntervalTensor.oneFibreEquiv_mk,
    LeftUnitIntervalTensor.oneFibreEquiv_mk, c.leftUnitOneEvaluation_representation]

end GradedKasparovCycle
end BC4lean.KKTheory
