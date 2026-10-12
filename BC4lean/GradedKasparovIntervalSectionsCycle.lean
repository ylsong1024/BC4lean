import BC4lean.GradedMatrixMoritaSectionRepresentation
import BC4lean.GradedKasparovSourcePullback

/-! # Genuine Kasparov correspondences on continuous sections

The intermediate algebra and the final coefficient algebra both vary
continuously. The representation acts pointwise and the Fredholm operator
is constant. Each localized defect is a norm-continuous field of actual
compact module operators, so the uniform finite-rank partition theorem
proves compactness on the section module. Neither a compact representation
nor a nondegenerate representation is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory

attribute [local instance]
  GradedMatrixMoritaSectionRepresentation.sourceSpectralOrder
  GradedMatrixMoritaSectionRepresentation.sourceSpectralOrderedRing

variable {Γ B C F X : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F]
  [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
  {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  {δB : CStarGrading B} {δC : CStarGrading C}

namespace GradedKasparovCycle

/-- A genuine second correspondence on continuous sections, for the
first-variable product homotopy construction. -/
def continuousSections (d : GradedKasparovCycle β γ δB δC F) :
    GradedKasparovCycle (β.continuousSections (X := X))
      (γ.continuousSections (X := X)) δB.continuousSections
      δC.continuousSections C(X, F) where
  sourceAction_preservesGrading :=
    CStarAlgebraAction.preservesGrading_continuousSections d.sourceAction_preservesGrading
  coefficientAction_preservesGrading :=
    CStarAlgebraAction.preservesGrading_continuousSections d.coefficientAction_preservesGrading
  countablyGenerated := continuousSection_isCountablyGenerated d.countablyGenerated
  grading := d.grading.gradedContinuousSections
  groupAction := d.groupAction.continuousSections
  grading_preserved := by
    intro g x
    ext t
    exact d.grading_preserved g (x t)
  representation := GradedMatrixMoritaSectionRepresentation.leftAction d.representation
  representation_graded := by
    intro b x
    ext t
    exact d.representation_graded (b t) (x t)
  representation_equivariant := by
    intro g b
    ext x t
    exact congrArg (fun T : AdjointableMap C F F => T (x t))
      (d.representation_equivariant g (b t))
  operator := continuousSectionConstantOperator d.operator
  operator_odd := by
    intro x
    ext t
    exact d.operator_odd (x t)
  selfadjoint_mod_compact := by
    intro b
    let ρ : C(X, AdjointableMap C F F) :=
      ⟨fun t => d.representation (b t),
        (GradedMatrixMoritaSectionRepresentation.leftActionCLM d.representation).continuous.comp
          b.continuous⟩
    let D : C(X, AdjointableMap C F F) :=
      ⟨fun t => (d.operator - star d.operator) * ρ t,
        continuous_const.mul ρ.continuous⟩
    have hD := continuousSectionOperator_isModuleCompact D
      (fun t => d.selfadjoint_mod_compact (b t))
    convert hD using 1
    ext x t
    rfl
  square_mod_compact := by
    intro b
    let ρ : C(X, AdjointableMap C F F) :=
      ⟨fun t => d.representation (b t),
        (GradedMatrixMoritaSectionRepresentation.leftActionCLM d.representation).continuous.comp
          b.continuous⟩
    let D : C(X, AdjointableMap C F F) :=
      ⟨fun t => (d.operator * d.operator - 1) * ρ t,
        continuous_const.mul ρ.continuous⟩
    have hD := continuousSectionOperator_isModuleCompact D
      (fun t => d.square_mod_compact (b t))
    convert hD using 1
    ext x t
    rfl
  commutator_compact := by
    intro b
    let ρ : C(X, AdjointableMap C F F) :=
      ⟨fun t => d.representation (b t),
        (GradedMatrixMoritaSectionRepresentation.leftActionCLM d.representation).continuous.comp
          b.continuous⟩
    let ρδ : C(X, AdjointableMap C F F) :=
      ⟨fun t => d.representation (δB.automorphism (b t)),
        (GradedMatrixMoritaSectionRepresentation.leftActionCLM d.representation).continuous.comp
          ((StarAlgEquiv.isometry δB.automorphism).continuous.comp b.continuous)⟩
    let D : C(X, AdjointableMap C F F) :=
      ⟨fun t => d.operator * ρ t - ρδ t * d.operator,
        (continuous_const.mul ρ.continuous).sub (ρδ.continuous.mul continuous_const)⟩
    have hD := continuousSectionOperator_isModuleCompact D
      (fun t => d.commutator_compact (b t))
    convert hD using 1
    ext x t
    rfl
  equivariance_mod_compact := by
    intro g b
    let ρ : C(X, AdjointableMap C F F) :=
      ⟨fun t => d.representation (b t),
        (GradedMatrixMoritaSectionRepresentation.leftActionCLM d.representation).continuous.comp
          b.continuous⟩
    let D : C(X, AdjointableMap C F F) :=
      ⟨fun t => (d.groupAction.conjugateOperator g d.operator - d.operator) * ρ t,
        continuous_const.mul ρ.continuous⟩
    have hD := continuousSectionOperator_isModuleCompact D
      (fun t => d.equivariance_mod_compact g (b t))
    convert hD using 1
    ext x t
    rfl

@[simp] theorem continuousSections_representation_apply
    (d : GradedKasparovCycle β γ δB δC F) (b : C(X, B)) (x : C(X, F)) (t : X) :
    d.continuousSections.representation b x t = d.representation (b t) (x t) := rfl

@[simp] theorem continuousSections_operator_apply
    (d : GradedKasparovCycle β γ δB δC F) (x : C(X, F)) (t : X) :
    d.continuousSections.operator x t = d.operator (x t) := rfl

@[simp] theorem continuousSections_grading_apply
    (d : GradedKasparovCycle β γ δB δC F) (x : C(X, F)) (t : X) :
    d.continuousSections.grading.grading x t = d.grading.grading (x t) := rfl

@[simp] theorem continuousSections_action_apply
    (d : GradedKasparovCycle β γ δB δC F) (g : Γ) (x : C(X, F)) (t : X) :
    d.continuousSections.groupAction.action g x t = d.groupAction.action g (x t) := rfl

/-- The actual completed section fibre is the original cycle pulled
back along evaluation of the continuous source algebra. -/
def continuousSectionsFibreIso
    (d : GradedKasparovCycle β γ δB δC F) (t : X) :
    GradedKasparovCycleIso (d.continuousSections.fibre t)
      (d.sourceEvaluationPullback t) where
  moduleEquiv := continuousSectionHilbertModuleFibreEquiv (B := C) (X := X) (E := F) t
  grading_intertwine z := by
    refine (hilbertModuleFibreMk_denseRange (B := C) (M := C(X, F)) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [GradedKasparovCycle.fibre_grading_mk,
        continuousSectionHilbertModuleFibreEquiv_mk,
        continuousSectionHilbertModuleFibreEquiv_mk]
      rfl
  action_intertwine g z := by
    refine (hilbertModuleFibreMk_denseRange (B := C) (M := C(X, F)) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [GradedKasparovCycle.fibre_action_mk,
        continuousSectionHilbertModuleFibreEquiv_mk,
        continuousSectionHilbertModuleFibreEquiv_mk]
      rfl
  representation_intertwine b z := by
    refine (hilbertModuleFibreMk_denseRange (B := C) (M := C(X, F)) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [GradedKasparovCycle.fibre_representation_mk,
        continuousSectionHilbertModuleFibreEquiv_mk,
        continuousSectionHilbertModuleFibreEquiv_mk]
      rfl
  operator_intertwine z := by
    refine (hilbertModuleFibreMk_denseRange (B := C) (M := C(X, F)) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [GradedKasparovCycle.fibre_operator_mk,
        continuousSectionHilbertModuleFibreEquiv_mk,
        continuousSectionHilbertModuleFibreEquiv_mk]
      rfl

end GradedKasparovCycle
end BC4lean.KKTheory
