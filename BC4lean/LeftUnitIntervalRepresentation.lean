import BC4lean.LeftUnitIntervalIdealGrading
import BC4lean.GradedIntervalKasparovNormalization
import BC4lean.GradedEquivariantInteriorModuleTensor

/-! # The unitized representation on sections, with only A-local defects

This is a representation and an operator on C(I,E), not a Kasparov cycle
over C(I,Unitization A). Scalar cancellation gives compact graded
commutators for all unitized coefficients. The other three compact defects
are proved only after multiplication by actual continuous A coefficients.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {Γ A B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [hAorder : PartialOrder A] [hAstarOrder : StarOrderedRing A]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

def leftUnitExtendedRepresentationCLM (φ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) :
    Unitization ℂ A →L[ℂ] AdjointableMap B E E :=
  ({ toFun := leftUnitExtendedRepresentation φ
     map_add' := map_add _
     map_smul' := map_smul _ } : Unitization ℂ A →ₗ[ℂ] AdjointableMap B E E).mkContinuous
    1 (fun u => by
      change ‖leftUnitExtendedRepresentation φ u‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using
        NonUnitalStarAlgHom.norm_apply_le (leftUnitExtendedRepresentation φ) u)

def leftUnitIntervalRepresentationField (φ : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (b : C(unitInterval, Unitization ℂ A)) : C(unitInterval, AdjointableMap B E E) :=
  ⟨fun t => leftUnitExtendedRepresentation φ (b t),
    (leftUnitExtendedRepresentationCLM φ).continuous.comp b.continuous⟩

def leftUnitIntervalSectionRepresentation (φ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) :
    C(unitInterval, Unitization ℂ A) →⋆ₙₐ[ℂ]
      AdjointableMap C(unitInterval, B) C(unitInterval, E) C(unitInterval, E) where
  toFun b := continuousSectionOperator (leftUnitIntervalRepresentationField φ b)
  map_zero' := by
    apply AdjointableMap.ext
    intro s
    apply ContinuousMap.ext
    intro t
    change leftUnitExtendedRepresentation φ (0 : Unitization ℂ A) (s t) = 0
    simp only [map_zero, AdjointableMap.coe_zero_apply]
  map_add' b d := by
    apply AdjointableMap.ext
    intro s
    apply ContinuousMap.ext
    intro t
    change leftUnitExtendedRepresentation φ (b t + d t) (s t) =
      leftUnitExtendedRepresentation φ (b t) (s t) + leftUnitExtendedRepresentation φ (d t) (s t)
    simp only [map_add, AdjointableMap.coe_add_apply]
  map_mul' b d := by
    apply AdjointableMap.ext
    intro s
    apply ContinuousMap.ext
    intro t
    change leftUnitExtendedRepresentation φ (b t * d t) (s t) =
      leftUnitExtendedRepresentation φ (b t) (leftUnitExtendedRepresentation φ (d t) (s t))
    simp only [map_mul, AdjointableMap.mul_apply]
  map_smul' z b := by
    apply AdjointableMap.ext
    intro s
    apply ContinuousMap.ext
    intro t
    change leftUnitExtendedRepresentation φ (z • b t) (s t) =
      z • leftUnitExtendedRepresentation φ (b t) (s t)
    simp only [map_smul, AdjointableMap.coe_smul_apply]
  map_star' b := by
    apply AdjointableMap.ext
    intro s
    apply ContinuousMap.ext
    intro t
    change leftUnitExtendedRepresentation φ (star (b t)) (s t) =
      star (leftUnitExtendedRepresentation φ (b t)) (s t)
    rw [map_star]

omit hAorder hAstarOrder in
@[simp] theorem leftUnitIntervalSectionRepresentation_apply
    [_hAorderDecl : PartialOrder A] [_hAstarOrderDecl : StarOrderedRing A]
    (φ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) (b : C(unitInterval, Unitization ℂ A))
    (s : C(unitInterval, E)) (t : unitInterval) :
    leftUnitIntervalSectionRepresentation φ b s t = leftUnitExtendedRepresentation φ (b t) (s t) := rfl

def leftUnitIntervalAEmbedding (a : C(unitInterval, A)) : C(unitInterval, Unitization ℂ A) :=
  ⟨fun t => (a t : Unitization ℂ A), Unitization.continuous_inr.comp a.continuous⟩

omit hAorder hAstarOrder in
@[simp] theorem leftUnitIntervalAEmbedding_apply
    [_hAorderDecl : PartialOrder A] [_hAstarOrderDecl : StarOrderedRing A] (a : C(unitInterval, A)) (t : unitInterval) :
    leftUnitIntervalAEmbedding a t = (a t : Unitization ℂ A) := rfl

variable {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

namespace GradedKasparovCycle
variable (c : GradedKasparovCycle α β δA δB E)

def leftUnitIntervalSecondOperator :
    AdjointableMap C(unitInterval, B) C(unitInterval, E) C(unitInterval, E) :=
  continuousSectionConstantOperator c.operator

omit hAorder hAstarOrder in
theorem leftUnitIntervalSecondRepresentation_graded
    [_hAorderDecl : PartialOrder A] [_hAstarOrderDecl : StarOrderedRing A] :
    ModuleTensorRepresentationGraded
      (δB := δA.leftUnitUnitization.continuousSections (X := unitInterval))
      (leftUnitIntervalSectionRepresentation c.representation) (c.grading.gradedContinuousSections (X := unitInterval)) := by
  intro b s
  apply ContinuousMap.ext
  intro t
  exact c.leftUnitExtendedRepresentation_graded (b t) (s t)

omit hAorder hAstarOrder in
theorem leftUnitIntervalSecondRepresentation_equivariant
    [_hAorderDecl : PartialOrder A] [_hAstarOrderDecl : StarOrderedRing A] :
    ModuleTensorRepresentationEquivariant (leftUnitIntervalSectionRepresentation c.representation)
      (α.leftUnitUnitization.continuousSections (X := unitInterval))
      (c.groupAction.continuousSections (X := unitInterval)) := by
  have h := EquivariantHilbertModule.representationEquivariant_of_conjugate
    (φ := (leftUnitExtendedRepresentation c.representation).toNonUnitalStarAlgHom)
    c.groupAction c.leftUnitExtendedRepresentation_equivariant
  intro g b s
  apply ContinuousMap.ext
  intro t
  exact h g (b t) (s t)

omit hAorder hAstarOrder in
theorem leftUnitIntervalSecondOperator_isOdd
    [_hAorderDecl : PartialOrder A] [_hAstarOrderDecl : StarOrderedRing A] :
    (c.grading.gradedContinuousSections (X := unitInterval)).IsOdd (c.grading.gradedContinuousSections (X := unitInterval))
      c.leftUnitIntervalSecondOperator := by
  intro s
  apply ContinuousMap.ext
  intro t
  exact c.operator_odd (s t)

omit hAorder hAstarOrder in
/-- All continuous unitized graded commutators are compact, by scalar cancellation
and the actual uniform finite-rank theorem for continuous compact fields. -/
theorem leftUnitIntervalSecond_commutator_compact
    [_hAorderDecl : PartialOrder A] [_hAstarOrderDecl : StarOrderedRing A] (b : C(unitInterval, Unitization ℂ A)) :
    IsModuleCompact (c.leftUnitIntervalSecondOperator *
        leftUnitIntervalSectionRepresentation c.representation b -
      leftUnitIntervalSectionRepresentation c.representation
        ((δA.leftUnitUnitization.continuousSections (X := unitInterval)).automorphism b) * c.leftUnitIntervalSecondOperator) := by
  let D : C(unitInterval, AdjointableMap B E E) :=
    ContinuousMap.const unitInterval c.operator * leftUnitIntervalRepresentationField c.representation b -
      leftUnitIntervalRepresentationField c.representation
        ((δA.leftUnitUnitization.continuousSections (X := unitInterval)).automorphism b) *
          ContinuousMap.const unitInterval c.operator
  have hD := continuousSectionOperator_isModuleCompact D
    (fun t => c.leftUnitExtendedRepresentation_commutator_compact (b t))
  convert hD using 1
  apply AdjointableMap.ext
  intro s
  apply ContinuousMap.ext
  intro t
  rfl

omit hAorder hAstarOrder in
theorem leftUnitIntervalSecond_localSelfadjoint_compact
    [_hAorderDecl : PartialOrder A] [_hAstarOrderDecl : StarOrderedRing A] (a : C(unitInterval, A)) :
    IsModuleCompact ((c.leftUnitIntervalSecondOperator - star c.leftUnitIntervalSecondOperator) *
      leftUnitIntervalSectionRepresentation c.representation (leftUnitIntervalAEmbedding a)) := by
  let D : C(unitInterval, AdjointableMap B E E) :=
    ⟨fun t => (c.operator - star c.operator) * c.representation (a t),
      continuous_const.mul ((AddMonoidHomClass.continuous_of_bound c.representation 1
        (by simpa only [one_mul] using! NonUnitalStarAlgHom.nnnorm_apply_le c.representation)).comp
          a.continuous)⟩
  have hD := continuousSectionOperator_isModuleCompact D (fun t => c.selfadjoint_mod_compact (a t))
  convert hD using 1
  apply AdjointableMap.ext
  intro s
  apply ContinuousMap.ext
  intro t
  change (c.operator - star c.operator)
    (leftUnitExtendedRepresentation c.representation (a t : Unitization ℂ A) (s t)) =
      (c.operator - star c.operator) (c.representation (a t) (s t))
  rw [leftUnitExtendedRepresentation_inr]

omit hAorder hAstarOrder in
theorem leftUnitIntervalSecond_localSquare_compact
    [_hAorderDecl : PartialOrder A] [_hAstarOrderDecl : StarOrderedRing A] (a : C(unitInterval, A)) :
    IsModuleCompact ((c.leftUnitIntervalSecondOperator * c.leftUnitIntervalSecondOperator - 1) *
      leftUnitIntervalSectionRepresentation c.representation (leftUnitIntervalAEmbedding a)) := by
  let D : C(unitInterval, AdjointableMap B E E) :=
    ⟨fun t => (c.operator * c.operator - 1) * c.representation (a t),
      continuous_const.mul ((AddMonoidHomClass.continuous_of_bound c.representation 1
        (by simpa only [one_mul] using! NonUnitalStarAlgHom.nnnorm_apply_le c.representation)).comp
          a.continuous)⟩
  have hD := continuousSectionOperator_isModuleCompact D (fun t => c.square_mod_compact (a t))
  convert hD using 1
  apply AdjointableMap.ext
  intro s
  apply ContinuousMap.ext
  intro t
  change (c.operator * c.operator - 1)
    (leftUnitExtendedRepresentation c.representation (a t : Unitization ℂ A) (s t)) =
      (c.operator * c.operator - 1) (c.representation (a t) (s t))
  rw [leftUnitExtendedRepresentation_inr]

omit hAorder hAstarOrder in
theorem leftUnitIntervalSecond_localEquivariance_compact
    [_hAorderDecl : PartialOrder A] [_hAstarOrderDecl : StarOrderedRing A] (g : Γ) (a : C(unitInterval, A)) :
    IsModuleCompact (((c.groupAction.continuousSections (X := unitInterval)).conjugateOperator g
        c.leftUnitIntervalSecondOperator - c.leftUnitIntervalSecondOperator) *
      leftUnitIntervalSectionRepresentation c.representation (leftUnitIntervalAEmbedding a)) := by
  let D : C(unitInterval, AdjointableMap B E E) :=
    ⟨fun t => (c.groupAction.conjugateOperator g c.operator - c.operator) * c.representation (a t),
      continuous_const.mul ((AddMonoidHomClass.continuous_of_bound c.representation 1
        (by simpa only [one_mul] using! NonUnitalStarAlgHom.nnnorm_apply_le c.representation)).comp
          a.continuous)⟩
  have hD := continuousSectionOperator_isModuleCompact D (fun t => c.equivariance_mod_compact g (a t))
  convert hD using 1
  apply AdjointableMap.ext
  intro s
  apply ContinuousMap.ext
  intro t
  change (c.groupAction.conjugateOperator g c.operator - c.operator)
    (leftUnitExtendedRepresentation c.representation (a t : Unitization ℂ A) (s t)) =
      (c.groupAction.conjugateOperator g c.operator - c.operator)
        (c.representation (a t) (s t))
  rw [leftUnitExtendedRepresentation_inr]

end GradedKasparovCycle
end BC4lean.KKTheory
