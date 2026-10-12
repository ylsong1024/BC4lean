import BC4lean.LeftUnitIntervalRankLocalization
import BC4lean.CompactFirstModuleConnection

/-! # The genuine localized left-unit interval cycle

The unitized second representation is used only for its graded commutators.
Square and group defects are localized by the actual compact left A action
on J. Their creation-range coefficients have continuous A preimages, so
the original cycle defects suffice. No Unitization cycle or essential-range
complement is assumed.
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

namespace GradedKasparovCycle
variable (c : GradedKasparovCycle α β δA δB E)
  {ξ : ℕ → LeftUnitIntervalIdeal A}
  (P : ModuleParsevalFrame (B := C(unitInterval, Unitization ℂ A)) ξ)
  (p : ℕ → Bool)
  (hξ : ∀ n, (leftUnitIntervalGrading δA).grading (ξ n) = if p n then -ξ n else ξ n)

def leftUnitIntervalConnectionOperator :
    AdjointableMap C(unitInterval, B) (LeftUnitIntervalTensor c.representation)
      (LeftUnitIntervalTensor c.representation) :=
  P.gradedConnection (leftUnitIntervalSectionRepresentation c.representation) p
    c.leftUnitIntervalSecondOperator

include hξ in
theorem leftUnitIntervalConnection_signed :
    IsSignedModuleConnection (leftUnitIntervalGrading δA)
      (leftUnitIntervalSectionRepresentation c.representation) c.leftUnitIntervalSecondOperator
      (c.leftUnitIntervalConnectionOperator P p) :=
  P.gradedConnection_isSignedModuleConnection (leftUnitIntervalGrading δA)
    (leftUnitIntervalSectionRepresentation c.representation) p hξ
    c.leftUnitIntervalSecondOperator c.leftUnitIntervalSecond_commutator_compact

theorem leftUnitIntervalSecond_selfadjoint (hsa : IsSelfAdjoint c.operator) :
    IsSelfAdjoint c.leftUnitIntervalSecondOperator := by
  let _retainedOriginalAOrder : PartialOrder A := inferInstance
  let _retainedOriginalAStarOrder : StarOrderedRing A := inferInstance
  change star c.leftUnitIntervalSecondOperator = c.leftUnitIntervalSecondOperator
  ext s t
  exact congrArg (fun T : AdjointableMap B E E => T (s t)) hsa.star_eq

theorem leftUnitIntervalConnection_selfadjoint (hsa : IsSelfAdjoint c.operator) :
    IsSelfAdjoint (c.leftUnitIntervalConnectionOperator P p) :=
  P.gradedConnection_selfadjoint (leftUnitIntervalSectionRepresentation c.representation) p
    (c.leftUnitIntervalSecond_selfadjoint hsa)

include hξ in
theorem leftUnitIntervalConnection_odd :
    c.leftUnitTensorGrading.IsOdd c.leftUnitTensorGrading
      (c.leftUnitIntervalConnectionOperator P p) :=
  P.gradedConnection_isOdd (leftUnitIntervalGrading δA) c.grading.gradedContinuousSections
    (leftUnitIntervalSectionRepresentation c.representation)
    c.leftUnitIntervalSecondRepresentation_graded p hξ c.leftUnitIntervalSecondOperator_isOdd

/-- A selfadjoint second defect localized by A gives a genuinely compact
creation defect on every vector in the actual left-A range. -/
theorem leftUnitLocalizedCreation_compact (a : A) (x : LeftUnitIntervalIdeal A)
    (T : AdjointableMap C(unitInterval, B) C(unitInterval, E) C(unitInterval, E))
    (hT : IsSelfAdjoint T)
    (hlocal : ∀ w : C(unitInterval, A), IsModuleCompact
      (T * leftUnitIntervalSectionRepresentation c.representation (leftUnitIntervalAEmbedding w))) :
    IsModuleCompact ((moduleCreationMap (leftUnitIntervalSectionRepresentation c.representation)
      (leftUnitIntervalRepresentation a x)).comp T) := by
  apply moduleCreationMap_comp_isModuleCompact_of_inner_local
  rw [← leftUnitIntervalLocalizedPairInner_inr a a x x, hT.star_eq]
  exact (hlocal (leftUnitIntervalLocalizedPairInner a a x x)).comp_right T

include hξ in
theorem leftUnitIntervalConnection_square_compact [TopologicalSpace.SeparableSpace A]
    (hsa : IsSelfAdjoint c.operator) (a : A) :
    IsModuleCompact (((c.leftUnitIntervalConnectionOperator P p) *
        (c.leftUnitIntervalConnectionOperator P p) - 1) * c.leftUnitTensorRepresentation a) := by
  let S := c.leftUnitIntervalSecondOperator
  have hS := c.leftUnitIntervalSecond_selfadjoint hsa
  have hD : IsSelfAdjoint (S * S - 1) := by
    change star (S * S - 1) = S * S - 1
    rw [star_sub, star_mul, star_one, hS.star_eq]
  let := leftUnitUnitization_separableSpace (A := A)
  let : TopologicalSpace.SeparableSpace C(unitInterval, Unitization ℂ A) := inferInstance
  apply tensorCompact_left_localization (leftUnitIntervalIdeal_countablyGenerated (A := A))
    (leftUnitIntervalSectionRepresentation c.representation) _ (leftUnitIntervalRepresentation a)
    (leftUnitIntervalRepresentation_isModuleCompact a)
  intro x
  exact (c.leftUnitIntervalConnection_signed P p hξ).square_comp_creation
    (leftUnitIntervalRepresentation a x)
    (c.leftUnitLocalizedCreation_compact a x (S * S - 1) hD
      c.leftUnitIntervalSecond_localSquare_compact)

include hξ in
set_option maxHeartbeats 400000 in
theorem leftUnitIntervalConnection_commutator_compact (a : A) :
    IsModuleCompact ((c.leftUnitIntervalConnectionOperator P p) * c.leftUnitTensorRepresentation a -
      c.leftUnitTensorRepresentation (δA.automorphism a) * (c.leftUnitIntervalConnectionOperator P p)) := by
  have hgrade : (leftUnitIntervalGrading δA).conjugateOperator (leftUnitIntervalRepresentation a) =
      leftUnitIntervalRepresentation (δA.automorphism a) := by
    ext x
    simp only [GradedHilbertModule.conjugateOperator_apply]
    rw [leftUnitIntervalRepresentation_graded, GradedHilbertModule.grading_sq]
  have h := (c.leftUnitIntervalConnection_signed P p hξ).graded_commutator_compact
    (leftUnitIntervalRepresentation_isModuleCompact a)
  rw [hgrade] at h
  exact h

include hξ in
set_option maxHeartbeats 400000 in
theorem leftUnitIntervalConnection_equivariance_compact [TopologicalSpace.SeparableSpace A]
    (hsa : IsSelfAdjoint c.operator) (g : Γ) (a : A) :
    IsModuleCompact ((c.leftUnitTensorAction.conjugateOperator g
        (c.leftUnitIntervalConnectionOperator P p) - c.leftUnitIntervalConnectionOperator P p) *
      c.leftUnitTensorRepresentation a) := by
  let V := c.groupAction.continuousSections (X := unitInterval)
  let S := c.leftUnitIntervalSecondOperator
  let D := V.conjugateOperator g S - S
  have hS := c.leftUnitIntervalSecond_selfadjoint hsa
  have hD : IsSelfAdjoint D := by
    have hSadj : S.adjoint = S := hS.star_eq
    change star (V.conjugateOperator g S - S) = V.conjugateOperator g S - S
    rw [star_sub, AdjointableMap.star_eq_adjoint, V.conjugateMap_adjoint V,
      hSadj, hS.star_eq]
  let := leftUnitUnitization_separableSpace (A := A)
  let : TopologicalSpace.SeparableSpace C(unitInterval, Unitization ℂ A) := inferInstance
  apply tensorCompact_left_localization (leftUnitIntervalIdeal_countablyGenerated (A := A))
    (leftUnitIntervalSectionRepresentation c.representation) _ (leftUnitIntervalRepresentation a)
    (leftUnitIntervalRepresentation_isModuleCompact a)
  intro x
  apply IsSignedModuleConnection.action_comp_creation (leftUnitIntervalGrading δA)
    (leftUnitIntervalAction α) V
    (leftUnitIntervalAction_preservesGrading c.sourceAction_preservesGrading)
    (leftUnitIntervalSectionRepresentation c.representation)
    c.leftUnitIntervalSecondRepresentation_equivariant
    (c.leftUnitIntervalConnection_signed P p hξ) g (leftUnitIntervalRepresentation a x)
  rw [leftUnitIntervalRepresentation_graded]
  exact c.leftUnitLocalizedCreation_compact (δA.automorphism a)
    ((leftUnitIntervalGrading δA).grading x) D hD
    (c.leftUnitIntervalSecond_localEquivariance_compact g)

include hξ in
/-- The actual homogeneous-frame connection is a genuine A,C(I,B) cycle.
The second representation has only the proved A-local defects. -/
def leftUnitIntervalConnectionCycle [TopologicalSpace.SeparableSpace A]
    (hsa : IsSelfAdjoint c.operator) :
    GradedKasparovCycle α (β.continuousSections (X := unitInterval)) δA (δB.continuousSections (X := unitInterval))
      (LeftUnitIntervalTensor c.representation) where
  sourceAction_preservesGrading := c.sourceAction_preservesGrading
  coefficientAction_preservesGrading :=
    CStarAlgebraAction.preservesGrading_continuousSections c.coefficientAction_preservesGrading
  countablyGenerated := leftUnitIntervalTensor_countablyGenerated c.representation c.countablyGenerated
  grading := c.leftUnitTensorGrading
  groupAction := c.leftUnitTensorAction
  grading_preserved := c.leftUnitTensorAction_preservesGrading
  representation := c.leftUnitTensorRepresentation
  representation_graded := c.leftUnitTensorRepresentation_graded
  representation_equivariant := c.leftUnitTensorRepresentation_equivariant
  operator := c.leftUnitIntervalConnectionOperator P p
  operator_odd := c.leftUnitIntervalConnection_odd P p hξ
  selfadjoint_mod_compact := by
    intro a
    rw [(c.leftUnitIntervalConnection_selfadjoint P p hsa).star_eq, sub_self, zero_mul]
    exact IsModuleCompact.zero
  square_mod_compact := c.leftUnitIntervalConnection_square_compact P p hξ hsa
  commutator_compact := c.leftUnitIntervalConnection_commutator_compact P p hξ
  equivariance_mod_compact := c.leftUnitIntervalConnection_equivariance_compact P p hξ hsa

theorem exists_leftUnitIntervalConnectionCycle [TopologicalSpace.SeparableSpace A]
    (hsa : IsSelfAdjoint c.operator) :
    ∃ (ξ : ℕ → LeftUnitIntervalIdeal A)
      (_P : ModuleParsevalFrame (B := C(unitInterval, Unitization ℂ A)) ξ)
      (p : ℕ → Bool)
      (_hξ : ∀ n, (leftUnitIntervalGrading δA).grading (ξ n) = if p n then -ξ n else ξ n),
      Nonempty (GradedKasparovCycle α (β.continuousSections (X := unitInterval)) δA (δB.continuousSections (X := unitInterval))
        (LeftUnitIntervalTensor c.representation)) := by
  obtain ⟨ξ, p, ⟨P⟩, hξ⟩ := leftUnitIntervalIdeal_exists_homogeneousParsevalFrame δA
  exact ⟨ξ, P, p, hξ, ⟨c.leftUnitIntervalConnectionCycle P p hξ hsa⟩⟩

end GradedKasparovCycle
end BC4lean.KKTheory
