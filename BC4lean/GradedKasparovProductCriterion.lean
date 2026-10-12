import BC4lean.GradedConnectionDefectAlgebra
import BC4lean.KasparovProductCriterion

/-! # The full product criterion for actual graded input cycles

The constructed tensor grading retains both coefficient gradings. The source
representation intertwines the actual source grading, and the cycle
commutator is the genuine graded one. The connection predicate contains
its four analytic compact laws; operator degree is proved separately.
Localized positivity is the actual positive-lift condition modulo module
compact endomorphisms. This criterion states no existence conclusion.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A B C E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}

variable (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)

def gradedKasparovTensorGrading :
    GradedHilbertModule δC (InteriorModuleTensor (E := E) d.representation) :=
  c.grading.interiorTensor d.grading d.representation_graded

def gradedKasparovTensorAction :
    EquivariantHilbertModule γ (InteriorModuleTensor (E := E) d.representation) :=
  c.groupAction.interiorTensor d.groupAction
    (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)

def gradedKasparovTensorRepresentation :
    A →⋆ₙₐ[ℂ] AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation) :=
  (interiorModuleTensorOperatorHom d.representation).toNonUnitalStarAlgHom.comp c.representation

@[simp] theorem gradedKasparovTensorRepresentation_apply (a : A) :
    gradedKasparovTensorRepresentation c d a =
      interiorModuleTensorOperator d.representation (c.representation a) := rfl

theorem gradedKasparovTensorRepresentation_graded (a : A)
    (u : InteriorModuleTensor (E := E) d.representation) :
    (gradedKasparovTensorGrading c d).grading (gradedKasparovTensorRepresentation c d a u) =
      gradedKasparovTensorRepresentation c d (δA.automorphism a)
        ((gradedKasparovTensorGrading c d).grading u) := by
  let J := (gradedKasparovTensorGrading c d).grading.toContinuousLinearEquiv.toContinuousLinearMap
  have heq : J.comp (gradedKasparovTensorRepresentation c d a).toCLM =
      (gradedKasparovTensorRepresentation c d (δA.automorphism a)).toCLM.comp J := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    have hφ : ModuleTensorRepresentationGraded (δB := δB) d.representation d.grading :=
      d.representation_graded
    change (c.grading.interiorTensor d.grading hφ).grading
        (interiorModuleTensorOperator d.representation (c.representation a)
          (interiorModuleTensorMk d.representation x y)) =
      interiorModuleTensorOperator d.representation (c.representation (δA.automorphism a))
        ((c.grading.interiorTensor d.grading hφ).grading
          (interiorModuleTensorMk d.representation x y))
    rw [interiorModuleTensorOperator_mk,
      GradedHilbertModule.interiorTensor_grading_mk,
      GradedHilbertModule.interiorTensor_grading_mk,
      interiorModuleTensorOperator_mk, c.representation_graded]
  exact DFunLike.congr_fun heq u

theorem gradedKasparovTensorAction_preservesGrading :
    (gradedKasparovTensorAction c d).PreservesGrading (gradedKasparovTensorGrading c d) :=
  c.groupAction.interiorTensor_preservesGrading d.groupAction c.grading d.grading
    c.grading_preserved d.grading_preserved
    (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)
    d.representation_graded

theorem gradedKasparovTensorRepresentation_equivariant (g : Γ) (a : A) :
    (gradedKasparovTensorAction c d).conjugateOperator g (gradedKasparovTensorRepresentation c d a) =
      gradedKasparovTensorRepresentation c d (α.automorphism g a) := by
  change (c.groupAction.interiorTensor d.groupAction _).conjugateOperator g
      (interiorModuleTensorOperator d.representation (c.representation a)) = _
  rw [EquivariantHilbertModule.interiorTensor_conjugateOperator, c.representation_equivariant]
  rfl

structure GradedKasparovTensorOperatorConditions
    (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) : Prop where
  operator_odd : (gradedKasparovTensorGrading c d).IsOdd (gradedKasparovTensorGrading c d) R
  selfadjoint_mod_compact : ∀ a,
    IsModuleCompact ((R - star R) * gradedKasparovTensorRepresentation c d a)
  square_mod_compact : ∀ a,
    IsModuleCompact ((R * R - 1) * gradedKasparovTensorRepresentation c d a)
  commutator_compact : ∀ a,
    IsModuleCompact (R * gradedKasparovTensorRepresentation c d a -
      gradedKasparovTensorRepresentation c d (δA.automorphism a) * R)
  equivariance_mod_compact : ∀ g a,
    IsModuleCompact (((gradedKasparovTensorAction c d).conjugateOperator g R - R) *
      gradedKasparovTensorRepresentation c d a)

def gradedKasparovTensorCycleOfConditions
    (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation))
    (hR : GradedKasparovTensorOperatorConditions c d R) :
    GradedKasparovCycle α γ δA δC (InteriorModuleTensor (E := E) d.representation) where
  sourceAction_preservesGrading := c.sourceAction_preservesGrading
  coefficientAction_preservesGrading := d.coefficientAction_preservesGrading
  countablyGenerated := c.countablyGenerated.interiorTensor d.countablyGenerated d.representation
  grading := gradedKasparovTensorGrading c d
  groupAction := gradedKasparovTensorAction c d
  grading_preserved := gradedKasparovTensorAction_preservesGrading c d
  representation := gradedKasparovTensorRepresentation c d
  representation_graded := gradedKasparovTensorRepresentation_graded c d
  representation_equivariant := gradedKasparovTensorRepresentation_equivariant c d
  operator := R
  operator_odd := hR.operator_odd
  selfadjoint_mod_compact := hR.selfadjoint_mod_compact
  square_mod_compact := hR.square_mod_compact
  commutator_compact := hR.commutator_compact
  equivariance_mod_compact := hR.equivariance_mod_compact

def gradedKasparovProductPositivityOperator
    (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) (a : A) :
    AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation) :=
  gradedKasparovTensorRepresentation c d a *
    (interiorModuleTensorOperator d.representation c.operator * R +
      R * interiorModuleTensorOperator d.representation c.operator) *
    star (gradedKasparovTensorRepresentation c d a)

structure IsGradedKasparovProductOperator
    (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) : Prop where
  cycleConditions : GradedKasparovTensorOperatorConditions c d R
  connection : GradedKasparovConnection c d R
  positivity : ∀ a, IsPositiveModuloModuleCompact (gradedKasparovProductPositivityOperator c d R a)

end BC4lean.KKTheory
