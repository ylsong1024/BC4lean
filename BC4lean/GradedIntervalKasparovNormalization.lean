import BC4lean.GradedKasparovNormalization
import BC4lean.FullGradedKasparovHomotopy

/-! # The full interval witness for genuine graded normalization

The actual affine operator homotopy gives a graded cycle on continuous
sections over C([0,1],B). Every compact defect is compact on that section
module, by the genuine uniform finite-rank partition theorem. Evaluation
of the completed Hilbert-module fibres gives whole-cycle isomorphisms with
the original and normalized endpoints, including both algebra gradings.
-/

noncomputable section
namespace BC4lean.KKTheory

open unitInterval
open scoped InnerProductSpace

variable {Γ A B E X : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- A genuine semilinear module grading acts pointwise on sections. -/
def GradedHilbertModule.gradedContinuousSections {δ : CStarGrading B}
    (γ : GradedHilbertModule δ E) :
    GradedHilbertModule (δ.continuousSections (X := X)) C(X, E) where
  grading := continuousSectionIsometryEquiv γ.grading
  involutive x := by ext t; exact γ.involutive (x t)
  inner_grading x y := by
    apply MulOpposite.unop_injective
    ext t
    exact congrArg MulOpposite.unop (γ.inner_grading (x t) (y t))

variable {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

namespace GradedKasparovOperatorHomotopy

variable {c : GradedKasparovCycle α β δA δB E} {T₀ T₁ : AdjointableMap B E E}

/-- The operator path supplies a genuine graded interval-coefficient cycle. -/
def intervalCycle (h : GradedKasparovOperatorHomotopy c T₀ T₁) :
    GradedKasparovCycle α (β.continuousSections (X := I))
      δA δB.continuousSections C(I, E) where
  sourceAction_preservesGrading := c.sourceAction_preservesGrading
  coefficientAction_preservesGrading :=
    CStarAlgebraAction.preservesGrading_continuousSections c.coefficientAction_preservesGrading
  countablyGenerated := continuousSection_isCountablyGenerated c.countablyGenerated
  grading := c.grading.gradedContinuousSections
  groupAction := c.groupAction.continuousSections
  grading_preserved := by
    intro g x
    ext t
    exact c.grading_preserved g (x t)
  representation := continuousSectionConstantOperatorHom.comp c.representation
  representation_graded := by
    intro a x
    ext t
    exact c.representation_graded a (x t)
  representation_equivariant := by
    intro g a
    ext x t
    exact congrArg (fun T : AdjointableMap B E E => T (x t))
      (c.representation_equivariant g a)
  operator := continuousSectionOperator ⟨h.path, h.path.continuous⟩
  operator_odd := by
    intro x
    ext t
    exact (h.conditions t).operator_odd (x t)
  selfadjoint_mod_compact := by
    intro a
    let D : C(I, AdjointableMap B E E) :=
      ⟨fun t => (h.path t - star (h.path t)) * c.representation a,
        (h.path.continuous.sub h.path.continuous.star).mul continuous_const⟩
    have hD := continuousSectionOperator_isModuleCompact D
      (fun t => (h.conditions t).selfadjoint_mod_compact a)
    convert hD using 1
    ext x t
    rfl
  square_mod_compact := by
    intro a
    let D : C(I, AdjointableMap B E E) :=
      ⟨fun t => (h.path t * h.path t - 1) * c.representation a,
        ((h.path.continuous.mul h.path.continuous).sub continuous_const).mul continuous_const⟩
    have hD := continuousSectionOperator_isModuleCompact D
      (fun t => (h.conditions t).square_mod_compact a)
    convert hD using 1
    ext x t
    rfl
  commutator_compact := by
    intro a
    let D : C(I, AdjointableMap B E E) :=
      ⟨fun t => h.path t * c.representation a -
          c.representation (δA.automorphism a) * h.path t,
        (h.path.continuous.mul continuous_const).sub (continuous_const.mul h.path.continuous)⟩
    have hD := continuousSectionOperator_isModuleCompact D
      (fun t => (h.conditions t).commutator_compact a)
    convert hD using 1
    ext x t
    rfl
  equivariance_mod_compact := by
    intro g a
    let D : C(I, AdjointableMap B E E) :=
      ⟨fun t => (c.groupAction.conjugateOperator g (h.path t) - h.path t) * c.representation a,
        (((c.groupAction.conjugateMapContinuousLinearMap c.groupAction g).continuous.comp
          h.path.continuous).sub h.path.continuous).mul continuous_const⟩
    have hD := continuousSectionOperator_isModuleCompact D
      (fun t => (h.conditions t).equivariance_mod_compact g a)
    convert hD using 1
    ext x t
    rfl

/-- Evaluation of the genuine completed interval fibre intertwines every
part of the graded cycle with the cycle at that parameter. -/
def intervalFibreIso (h : GradedKasparovOperatorHomotopy c T₀ T₁) (t : I) :
    GradedKasparovCycleIso (h.intervalCycle.fibre t) (h.cycleAt t) where
  moduleEquiv := continuousSectionHilbertModuleFibreEquiv (B := B) t
  grading_intertwine z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := C(I, E)) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [GradedKasparovCycle.fibre_grading_mk,
        continuousSectionHilbertModuleFibreEquiv_mk,
        continuousSectionHilbertModuleFibreEquiv_mk]
      rfl
  action_intertwine g z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := C(I, E)) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [GradedKasparovCycle.fibre_action_mk,
        continuousSectionHilbertModuleFibreEquiv_mk,
        continuousSectionHilbertModuleFibreEquiv_mk]
      rfl
  representation_intertwine a z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := C(I, E)) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [GradedKasparovCycle.fibre_representation_mk,
        continuousSectionHilbertModuleFibreEquiv_mk,
        continuousSectionHilbertModuleFibreEquiv_mk]
      rfl
  operator_intertwine z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := C(I, E)) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [GradedKasparovCycle.fibre_operator_mk,
        continuousSectionHilbertModuleFibreEquiv_mk,
        continuousSectionHilbertModuleFibreEquiv_mk]
      rfl

def intervalFibreZeroIso (h : GradedKasparovOperatorHomotopy c T₀ T₁) :
    GradedKasparovCycleIso (h.intervalCycle.fibre 0) (c.withOperator T₀ h.source_conditions) := by
  simpa only [source_cycleAt] using h.intervalFibreIso 0

def intervalFibreOneIso (h : GradedKasparovOperatorHomotopy c T₀ T₁) :
    GradedKasparovCycleIso (h.intervalCycle.fibre 1) (c.withOperator T₁ h.target_conditions) := by
  simpa only [target_cycleAt] using h.intervalFibreIso 1

/-- The path gives one genuine full interval witness, with actual endpoint
whole-cycle identifications. -/
def fullHomotopy (h : GradedKasparovOperatorHomotopy c T₀ T₁) :
    FullGradedKasparovHomotopy
      (BundledGradedKasparovCycle.of (c.withOperator T₀ h.source_conditions))
      (BundledGradedKasparovCycle.of (c.withOperator T₁ h.target_conditions)) where
  intervalCycle := BundledGradedKasparovCycle.of h.intervalCycle
  sourceIso := h.intervalFibreZeroIso
  targetIso := h.intervalFibreOneIso

end GradedKasparovOperatorHomotopy

namespace GradedKasparovCycle

/-- Every arbitrary genuine graded cycle is fully interval-homotopic to its
proved selfadjoint contractive normalization on the same module. -/
def fullNormalizationHomotopy (c : GradedKasparovCycle α β δA δB E) :
    FullGradedKasparovHomotopy (BundledGradedKasparovCycle.of c)
      (BundledGradedKasparovCycle.of c.normalized) := by
  simpa only [GradedKasparovCycle.withOperator_self, normalized,
    GradedKasparovCycle.withOperator_operator] using
    c.normalizationHomotopy.fullHomotopy

end GradedKasparovCycle
end BC4lean.KKTheory
