import BC4lean.GradedKasparovProductCriterion
import BC4lean.ModuleTensorCompact

/-! # An actual genuinely graded product for a compact second representation

Both source and coefficient gradings are retained. If the second cycle has zero operator and compact left representation, the
actual first-factor operator `T ⊗ 1` satisfies the full Kasparov product
criterion. All four cycle defects are induced from the first cycle. The four
connection defects are compositions with proved compact creation maps.
Localized positivity has the explicit positive lift `2 φ(a) φ(a)*`, whose
error is compact by the actual square defect. This is a product existence
theorem under its displayed special hypotheses; general product existence
requires the separate technical theorem.
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

/-- Induction of all actual first-cycle defects when the second left action
is compact. This operator condition itself does not require a zero second operator. -/
theorem gradedKasparovTensorOperatorConditions_of_compact_second_representation
    (hd : ∀ b, IsModuleCompact (d.representation b)) :
    GradedKasparovTensorOperatorConditions c d
      (interiorModuleTensorOperator d.representation c.operator) where
  operator_odd := GradedHilbertModule.IsOdd.interiorModuleTensorOperator
    d.grading d.representation_graded c.operator_odd
  selfadjoint_mod_compact a := by
    have h := (c.selfadjoint_mod_compact a).interiorModuleTensorOperator d.representation hd
    change IsModuleCompact ((interiorModuleTensorOperatorHom d.representation)
      ((c.operator - star c.operator) * c.representation a)) at h
    simpa only [map_mul, map_sub, map_star, interiorModuleTensorOperatorHom_apply,
      gradedKasparovTensorRepresentation_apply] using h
  square_mod_compact a := by
    have h := (c.square_mod_compact a).interiorModuleTensorOperator d.representation hd
    change IsModuleCompact ((interiorModuleTensorOperatorHom d.representation)
      ((c.operator * c.operator - 1) * c.representation a)) at h
    simpa only [map_mul, map_sub, map_one, interiorModuleTensorOperatorHom_apply,
      gradedKasparovTensorRepresentation_apply] using h
  commutator_compact a := by
    have h := (c.commutator_compact a).interiorModuleTensorOperator d.representation hd
    change IsModuleCompact ((interiorModuleTensorOperatorHom d.representation)
      (c.operator * c.representation a - c.representation (δA.automorphism a) * c.operator)) at h
    simpa only [map_sub, map_mul, interiorModuleTensorOperatorHom_apply,
      gradedKasparovTensorRepresentation_apply] using h
  equivariance_mod_compact g a := by
    have h := (c.equivariance_mod_compact g a).interiorModuleTensorOperator d.representation hd
    change IsModuleCompact ((interiorModuleTensorOperatorHom d.representation)
      ((c.groupAction.conjugateOperator g c.operator - c.operator) * c.representation a)) at h
    change IsModuleCompact (((c.groupAction.interiorTensor d.groupAction _).conjugateOperator g
      (interiorModuleTensorOperator d.representation c.operator) -
        interiorModuleTensorOperator d.representation c.operator) *
        gradedKasparovTensorRepresentation c d a)
    rw [EquivariantHilbertModule.interiorTensor_conjugateOperator]
    simpa only [map_mul, map_sub, interiorModuleTensorOperatorHom_apply,
      gradedKasparovTensorRepresentation_apply] using h

/-- Compact creation maps supply all four homogeneous connection defects
when the actual second cycle operator vanishes. -/
theorem gradedKasparovConnection_of_zero_compact_second
    (hzero : d.operator = 0) (hd : ∀ b, IsModuleCompact (d.representation b)) :
    GradedKasparovConnection c d (interiorModuleTensorOperator d.representation c.operator) := by
  have hcomp (ξ : E) : (moduleCreationMap d.representation ξ).comp
      (0 : AdjointableMap C F F) = 0 := by
    apply AdjointableMap.ext
    intro y
    change (moduleCreationMap d.representation ξ).toCLM 0 = 0
    exact map_zero _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ξ _
    rw [hzero]
    simpa only [hcomp, zero_sub] using
      ((moduleCreationMap_isModuleCompact_of_compact_left_action
        d.representation hd ξ).comp_left
          (interiorModuleTensorOperator d.representation c.operator)).neg
  · intro ξ _
    rw [hzero, star_zero]
    simpa only [hcomp, zero_sub] using
      ((moduleCreationMap_isModuleCompact_of_compact_left_action
        d.representation hd ξ).comp_left
          (star (interiorModuleTensorOperator d.representation c.operator))).neg
  · intro ξ _
    rw [hzero]
    simpa only [hcomp, zero_add] using
      (moduleCreationMap_isModuleCompact_of_compact_left_action
        d.representation hd ξ).comp_left
          (interiorModuleTensorOperator d.representation c.operator)
  · intro ξ _
    rw [hzero, star_zero]
    simpa only [hcomp, zero_add] using
      (moduleCreationMap_isModuleCompact_of_compact_left_action
        d.representation hd ξ).comp_left
          (star (interiorModuleTensorOperator d.representation c.operator))

local instance gradedKasparovCompactSecondProductLocalInstance1 : PartialOrder
    (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) := CStarAlgebra.spectralOrder _
local instance gradedKasparovCompactSecondProductLocalInstance2 : StarOrderedRing
    (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) := CStarAlgebra.spectralOrderedRing _

/-- The square defect supplies the explicit localized positive lift for
the first-factor tensor operator. -/
theorem gradedKasparovProductPositivity_of_compact_second_representation
    (hd : ∀ b, IsModuleCompact (d.representation b)) (a : A) :
    IsPositiveModuloModuleCompact (gradedKasparovProductPositivityOperator c d
      (interiorModuleTensorOperator d.representation c.operator) a) := by
  let R := interiorModuleTensorOperator d.representation c.operator
  let p := gradedKasparovTensorRepresentation c d a
  have hsq : IsModuleCompact ((R * R - 1) * star p) := by
    have h := (c.square_mod_compact (star a)).interiorModuleTensorOperator d.representation hd
    change IsModuleCompact ((interiorModuleTensorOperatorHom d.representation)
      ((c.operator * c.operator - 1) * c.representation (star a))) at h
    simpa only [map_mul, map_sub, map_one, map_star,
      interiorModuleTensorOperatorHom_apply, R, p, gradedKasparovTensorRepresentation_apply] using h
  refine ⟨p * star p + p * star p,
    add_nonneg (mul_star_self_nonneg p) (mul_star_self_nonneg p), ?_⟩
  have heq : gradedKasparovProductPositivityOperator c d R a -
      (p * star p + p * star p) =
      p * ((R * R - 1) * star p) + p * ((R * R - 1) * star p) := by
    dsimp only [gradedKasparovProductPositivityOperator, R, p]
    noncomm_ring
  rw [heq]
  exact IsModuleCompact.add
    (mul_mem_moduleCompact_left p hsq) (mul_mem_moduleCompact_left p hsq)

/-- A genuine product operator on the actual interior tensor under the
compact-representation, zero-operator hypothesis on the second cycle. -/
theorem isGradedKasparovProductOperator_of_zero_compact_second
    (hzero : d.operator = 0) (hd : ∀ b, IsModuleCompact (d.representation b)) :
    IsGradedKasparovProductOperator c d
      (interiorModuleTensorOperator d.representation c.operator) where
  cycleConditions := gradedKasparovTensorOperatorConditions_of_compact_second_representation c d hd
  connection := gradedKasparovConnection_of_zero_compact_second c d hzero hd
  positivity := gradedKasparovProductPositivity_of_compact_second_representation c d hd

/-- The resulting actual complete, graded, equivariant tensor cycle. -/
def gradedKasparovCompactSecondProduct
    (hd : ∀ b, IsModuleCompact (d.representation b)) :
    GradedKasparovCycle α γ δA δC (InteriorModuleTensor (E := E) d.representation) :=
  gradedKasparovTensorCycleOfConditions c d
    (interiorModuleTensorOperator d.representation c.operator)
    (gradedKasparovTensorOperatorConditions_of_compact_second_representation c d hd)

/-- The constructed cycle operator satisfies every product condition
when the second operator is zero. -/
theorem gradedKasparovCompactSecondProduct_isProduct
    (hzero : d.operator = 0) (hd : ∀ b, IsModuleCompact (d.representation b)) :
    IsGradedKasparovProductOperator c d (gradedKasparovCompactSecondProduct c d hd).operator :=
  isGradedKasparovProductOperator_of_zero_compact_second c d hzero hd

end BC4lean.KKTheory
