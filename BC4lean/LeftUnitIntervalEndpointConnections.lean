import BC4lean.LeftUnitIntervalConnectionCycle
import BC4lean.RectangularModuleFibreOperator
import BC4lean.GradedKasparovTensorCycleTransport
import BC4lean.GradedKasparovCycleOperatorTransport
import BC4lean.GradedStandardIdentityCycle

/-! # Actual endpoint connection and compact-perturbation identities

The completed endpoint unitaries evaluate every creation map. At zero the
scalar ramp gives the identity creation range; at one the ideal coefficient
gives the usual A tensor creation map. Compactness descends through the
actual rectangular fibre map, including the independent adjoint law.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {Γ A B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [endpointOrderA : PartialOrder A] [endpointStarOrderA : StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

namespace GradedKasparovCycle
variable (c : GradedKasparovCycle α β δA δB E)
  {ξ : ℕ → LeftUnitIntervalIdeal A}
  (P : ModuleParsevalFrame (B := C(unitInterval, Unitization ℂ A)) ξ) (p : ℕ → Bool)

def leftUnitZeroOperator : AdjointableMap B E E :=
  (LeftUnitIntervalTensor.zeroFibreEquiv c.representation).transport
    (hilbertModuleFibreOperator 0 (c.leftUnitIntervalConnectionOperator P p))

def leftUnitOneOperator : AdjointableMap B (InteriorModuleTensor (E := Aᵐᵒᵖ) c.representation)
    (InteriorModuleTensor (E := Aᵐᵒᵖ) c.representation) :=
  (LeftUnitIntervalTensor.oneFibreEquiv c.representation).transport
    (hilbertModuleFibreOperator 1 (c.leftUnitIntervalConnectionOperator P p))

set_option maxHeartbeats 1200000 in
theorem leftUnitZero_creation (j : LeftUnitIntervalIdeal A)
    (z : HilbertModuleFibre B C(unitInterval, E) (0 : unitInterval)) :
    LeftUnitIntervalTensor.zeroFibreEquiv c.representation
      (hilbertModuleFibreRectangularMap 0
        (moduleCreationMap (leftUnitIntervalSectionRepresentation c.representation) j) z) =
      leftUnitExtendedRepresentation c.representation
        (MulOpposite.unop (j : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 0)
        (continuousSectionHilbertModuleFibreEquiv (B := B) 0 z) := by
  obtain ⟨s, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) 0 z
  rw [hilbertModuleFibreRectangularMap_mk]
  change LeftUnitIntervalTensor.zeroFibreEquiv c.representation
    (hilbertModuleFibreMk (B := B) (X := unitInterval)
      (M := LeftUnitIntervalTensor c.representation) (0 : unitInterval)
      (interiorModuleTensorMk
        (B := C(unitInterval, Unitization ℂ A)) (C := C(unitInterval, B))
        (E := LeftUnitIntervalIdeal A) (F := C(unitInterval, E))
        (leftUnitIntervalSectionRepresentation c.representation) j s)) = _
  rw [LeftUnitIntervalTensor.zeroFibreEquiv_tensor_mk,
    continuousSectionHilbertModuleFibreEquiv_mk]

set_option maxHeartbeats 1200000 in
theorem leftUnitOne_creation (j : LeftUnitIntervalIdeal A)
    (z : HilbertModuleFibre B C(unitInterval, E) (1 : unitInterval)) :
    LeftUnitIntervalTensor.oneFibreEquiv c.representation
      (hilbertModuleFibreRectangularMap 1
        (moduleCreationMap (leftUnitIntervalSectionRepresentation c.representation) j) z) =
      moduleCreationMap c.representation (LeftUnitIntervalTensor.oneCoefficient j)
        (continuousSectionHilbertModuleFibreEquiv (B := B) 1 z) := by
  obtain ⟨s, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) 1 z
  rw [hilbertModuleFibreRectangularMap_mk]
  change LeftUnitIntervalTensor.oneFibreEquiv c.representation
    (hilbertModuleFibreMk (B := B) (X := unitInterval)
      (M := LeftUnitIntervalTensor c.representation) (1 : unitInterval)
      (interiorModuleTensorMk
        (B := C(unitInterval, Unitization ℂ A)) (C := C(unitInterval, B))
        (E := LeftUnitIntervalIdeal A) (F := C(unitInterval, E))
        (leftUnitIntervalSectionRepresentation c.representation) j s)) = _
  rw [LeftUnitIntervalTensor.oneFibreEquiv_tensor_mk,
    continuousSectionHilbertModuleFibreEquiv_mk]
  rfl

omit endpointOrderA endpointStarOrderA in
theorem leftUnitSecondFibre_intertwine [PartialOrder A] [StarOrderedRing A] (t : unitInterval)
    (z : HilbertModuleFibre B C(unitInterval, E) t) :
    continuousSectionHilbertModuleFibreEquiv (B := B) t
      (hilbertModuleFibreOperator t c.leftUnitIntervalSecondOperator z) =
      c.operator (continuousSectionHilbertModuleFibreEquiv (B := B) t z) := by
  obtain ⟨s, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) t z
  rw [hilbertModuleFibreOperator_mk, continuousSectionHilbertModuleFibreEquiv_mk,
    continuousSectionHilbertModuleFibreEquiv_mk]
  rfl

omit endpointOrderA endpointStarOrderA in
theorem leftUnitSecondFibre_star_intertwine [PartialOrder A] [StarOrderedRing A] (t : unitInterval)
    (z : HilbertModuleFibre B C(unitInterval, E) t) :
    continuousSectionHilbertModuleFibreEquiv (B := B) t
      (hilbertModuleFibreOperator t (star c.leftUnitIntervalSecondOperator) z) =
      star c.operator (continuousSectionHilbertModuleFibreEquiv (B := B) t z) := by
  obtain ⟨s, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) t z
  rw [hilbertModuleFibreOperator_mk, continuousSectionHilbertModuleFibreEquiv_mk,
    continuousSectionHilbertModuleFibreEquiv_mk]
  rfl

theorem leftUnitOneCoefficient_grading (j : LeftUnitIntervalIdeal A) :
    LeftUnitIntervalTensor.oneCoefficient ((leftUnitIntervalGrading δA).grading j) =
      (GradedHilbertModule.standard δA).grading (LeftUnitIntervalTensor.oneCoefficient j) := rfl

theorem leftUnitOneCoefficient_surjective :
    Function.Surjective (LeftUnitIntervalTensor.oneCoefficient (A := A)) := by
  intro a
  refine ⟨leftUnitIntervalASection (MulOpposite.op (ContinuousMap.const unitInterval
    (MulOpposite.unop a))), ?_⟩
  apply MulOpposite.unop_injective
  exact Unitization.snd_inr (R := ℂ) (MulOpposite.unop a)

section GeneralDefect
variable (G : AdjointableMap C(unitInterval, B) (LeftUnitIntervalTensor c.representation)
    (LeftUnitIntervalTensor c.representation))
  (S : AdjointableMap C(unitInterval, B) C(unitInterval, E) C(unitInterval, E))
  (S₀ : AdjointableMap B E E)
  (hS : ∀ z, continuousSectionHilbertModuleFibreEquiv (B := B) (1 : unitInterval)
    (hilbertModuleFibreOperator 1 S z) =
      S₀ (continuousSectionHilbertModuleFibreEquiv (B := B) 1 z))

include hS in
theorem leftUnitOne_signedCreation_defect (j : LeftUnitIntervalIdeal A) :
    (continuousSectionHilbertModuleFibreEquiv (B := B) (1 : unitInterval)).transportMap
      (LeftUnitIntervalTensor.oneFibreEquiv c.representation)
      (hilbertModuleFibreRectangularMap 1
        (G.comp (moduleCreationMap (leftUnitIntervalSectionRepresentation c.representation) j) -
          (moduleCreationMap (leftUnitIntervalSectionRepresentation c.representation)
            ((leftUnitIntervalGrading δA).grading j)).comp S)) =
      ((LeftUnitIntervalTensor.oneFibreEquiv c.representation).transport
        (hilbertModuleFibreOperator 1 G)).comp
          (moduleCreationMap c.representation (LeftUnitIntervalTensor.oneCoefficient j)) -
        (moduleCreationMap c.representation
          ((GradedHilbertModule.standard δA).grading (LeftUnitIntervalTensor.oneCoefficient j))).comp S₀ := by
  have hG (z : HilbertModuleFibre B (LeftUnitIntervalTensor c.representation) (1 : unitInterval)) :
      LeftUnitIntervalTensor.oneFibreEquiv c.representation (hilbertModuleFibreOperator 1 G z) =
        (LeftUnitIntervalTensor.oneFibreEquiv c.representation).transport
          (hilbertModuleFibreOperator 1 G) (LeftUnitIntervalTensor.oneFibreEquiv c.representation z) := by
    simp only [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply]
  ext y
  simp only [HilbertModuleEquiv.transportMap_apply, hilbertModuleFibreRectangularMap_sub,
    hilbertModuleFibreRectangularMap_comp, hilbertModuleFibreRectangularMap_eq_operator,
    AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply, map_sub, hG,
    c.leftUnitOne_creation, leftUnitOneCoefficient_grading, hS,
    HilbertModuleEquiv.apply_symm_apply]

end GeneralDefect

set_option maxHeartbeats 1200000 in
theorem leftUnitZeroOperator_sub_compact
    (hξ : ∀ n, (leftUnitIntervalGrading δA).grading (ξ n) = if p n then -ξ n else ξ n) :
    IsModuleCompact (c.leftUnitZeroOperator P p - c.operator) := by
  let j := leftUnitIntervalRamp (MulOpposite.op (1 : Unitization ℂ A))
  have hj : MulOpposite.unop (j : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 0 = 1 := by
    exact congrArg MulOpposite.unop (leftUnitIntervalEvaluation_zero_ramp _)
  have hJj : MulOpposite.unop ((leftUnitIntervalGrading δA).grading j :
      C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 0 = 1 := by
    rw [leftUnitIntervalGrading_apply, hj, map_one]
  have h := (continuousSectionHilbertModuleFibreEquiv (B := B) (0 : unitInterval)).transportMap_isModuleCompact
    (LeftUnitIntervalTensor.zeroFibreEquiv c.representation)
    (((c.leftUnitIntervalConnection_signed P p hξ).creation j).rectangular_fibre 0)
  have hG (z : HilbertModuleFibre B (LeftUnitIntervalTensor c.representation) (0 : unitInterval)) :
      LeftUnitIntervalTensor.zeroFibreEquiv c.representation
        (hilbertModuleFibreOperator 0 (c.leftUnitIntervalConnectionOperator P p) z) =
      c.leftUnitZeroOperator P p (LeftUnitIntervalTensor.zeroFibreEquiv c.representation z) := by
    simp only [leftUnitZeroOperator, HilbertModuleEquiv.transport_apply,
      HilbertModuleEquiv.symm_apply_apply]
  convert h using 1
  ext y
  simp only [HilbertModuleEquiv.transportMap_apply,
    hilbertModuleFibreRectangularMap_sub, hilbertModuleFibreRectangularMap_comp,
    hilbertModuleFibreRectangularMap_eq_operator, AdjointableMap.comp_apply,
    AdjointableMap.coe_sub_apply, map_sub, hG, c.leftUnitZero_creation,
    c.leftUnitSecondFibre_intertwine, hj, hJj, map_one, AdjointableMap.one_apply,
    HilbertModuleEquiv.apply_symm_apply]

theorem leftUnitOneOperator_signed
    (hξ : ∀ n, (leftUnitIntervalGrading δA).grading (ξ n) = if p n then -ξ n else ξ n) :
    IsSignedModuleConnection (GradedHilbertModule.standard δA) c.representation c.operator
      (c.leftUnitOneOperator P p) := by
  constructor
  · intro a
    obtain ⟨j, rfl⟩ := leftUnitOneCoefficient_surjective a
    have h := (continuousSectionHilbertModuleFibreEquiv (B := B) (1 : unitInterval)).transportMap_isModuleCompact
      (LeftUnitIntervalTensor.oneFibreEquiv c.representation)
      (((c.leftUnitIntervalConnection_signed P p hξ).creation j).rectangular_fibre 1)
    rwa [c.leftUnitOne_signedCreation_defect (c.leftUnitIntervalConnectionOperator P p)
      c.leftUnitIntervalSecondOperator c.operator (c.leftUnitSecondFibre_intertwine 1) j] at h
  · intro a
    obtain ⟨j, rfl⟩ := leftUnitOneCoefficient_surjective a
    have h := (continuousSectionHilbertModuleFibreEquiv (B := B) (1 : unitInterval)).transportMap_isModuleCompact
      (LeftUnitIntervalTensor.oneFibreEquiv c.representation)
      (((c.leftUnitIntervalConnection_signed P p hξ).creation_adjoint j).rectangular_fibre 1)
    rw [c.leftUnitOne_signedCreation_defect (star (c.leftUnitIntervalConnectionOperator P p))
      (star c.leftUnitIntervalSecondOperator) (star c.operator)
      (c.leftUnitSecondFibre_star_intertwine 1) j] at h
    simpa only [leftUnitOneOperator, hilbertModuleFibreOperator_star,
      HilbertModuleEquiv.transport_star] using h

section EndpointCycles
variable [TopologicalSpace.SeparableSpace A]
  (hξ : ∀ n, (leftUnitIntervalGrading δA).grading (ξ n) = if p n then -ξ n else ξ n)
  (hsa : IsSelfAdjoint c.operator)

include hξ hsa

theorem leftUnitZeroOperator_conditions : c.OperatorConditions (c.leftUnitZeroOperator P p) :=
  transportedCycle_fixedOperatorConditions ((c.leftUnitIntervalConnectionCycle P p hξ hsa).fibre 0) c
    (LeftUnitIntervalTensor.zeroFibreEquiv c.representation)
    c.leftUnitZeroFibreEquiv_grading c.leftUnitZeroFibreEquiv_action
    c.leftUnitZeroFibreEquiv_representation

def leftUnitZeroCycleIso : GradedKasparovCycleIso
    ((c.leftUnitIntervalConnectionCycle P p hξ hsa).fibre 0)
    (c.withOperator (c.leftUnitZeroOperator P p) (c.leftUnitZeroOperator_conditions P p hξ hsa)) :=
  transportedCycle_fixedIso ((c.leftUnitIntervalConnectionCycle P p hξ hsa).fibre 0) c
    (LeftUnitIntervalTensor.zeroFibreEquiv c.representation)
    c.leftUnitZeroFibreEquiv_grading c.leftUnitZeroFibreEquiv_action
    c.leftUnitZeroFibreEquiv_representation

theorem leftUnitOneOperator_conditions :
    GradedKasparovTensorOperatorConditions
      (gradedStandardIdentityCycle α δA c.sourceAction_preservesGrading) c (c.leftUnitOneOperator P p) :=
  transportedCycle_tensorConditions
    (gradedStandardIdentityCycle α δA c.sourceAction_preservesGrading) c
    ((c.leftUnitIntervalConnectionCycle P p hξ hsa).fibre 1)
    (LeftUnitIntervalTensor.oneFibreEquiv c.representation)
    c.leftUnitOneFibreEquiv_grading c.leftUnitOneFibreEquiv_action
    c.leftUnitOneFibreEquiv_representation

theorem leftUnitOneOperator_isProduct : IsGradedKasparovProductOperator
    (gradedStandardIdentityCycle α δA c.sourceAction_preservesGrading) c (c.leftUnitOneOperator P p) where
  cycleConditions := c.leftUnitOneOperator_conditions P p hξ hsa
  connection := IsSignedModuleConnection.gradedKasparovConnection
    (gradedStandardIdentityCycle α δA c.sourceAction_preservesGrading) c
    (c.leftUnitOneOperator_signed P p hξ)
  positivity a := by
    change IsPositiveModuloModuleCompact
      (gradedKasparovTensorRepresentation (gradedStandardIdentityCycle α δA c.sourceAction_preservesGrading) c a *
        (interiorModuleTensorOperator c.representation 0 * c.leftUnitOneOperator P p +
          c.leftUnitOneOperator P p * interiorModuleTensorOperator c.representation 0) * _)
    rw [show interiorModuleTensorOperator c.representation
      (0 : AdjointableMap A Aᵐᵒᵖ Aᵐᵒᵖ) = 0 from map_zero (interiorModuleTensorOperatorHom c.representation)]
    simp only [zero_mul, mul_zero, zero_add]
    exact IsModuleCompact.zero.isPositiveModuloModuleCompact

def leftUnitOneCycleIso : GradedKasparovCycleIso
    ((c.leftUnitIntervalConnectionCycle P p hξ hsa).fibre 1)
    (gradedKasparovTensorCycleOfConditions
      (gradedStandardIdentityCycle α δA c.sourceAction_preservesGrading) c
      (c.leftUnitOneOperator P p) (c.leftUnitOneOperator_isProduct P p hξ hsa).cycleConditions) :=
  transportedCycle_tensorIso
    (gradedStandardIdentityCycle α δA c.sourceAction_preservesGrading) c
    ((c.leftUnitIntervalConnectionCycle P p hξ hsa).fibre 1)
    (LeftUnitIntervalTensor.oneFibreEquiv c.representation)
    c.leftUnitOneFibreEquiv_grading c.leftUnitOneFibreEquiv_action
    c.leftUnitOneFibreEquiv_representation

end EndpointCycles
end GradedKasparovCycle
end BC4lean.KKTheory
