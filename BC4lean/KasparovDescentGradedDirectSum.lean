import BC4lean.KasparovDescentGradedCycle
import BC4lean.KasparovDescentDirectSum
import BC4lean.GradedKasparovDirectSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Genuine direct-sum compatibility of fully graded reduced descent

The actual completed coefficient-form distributivity unitary intertwines
the induced semilinear grading. The existing completed-source and operator
intertwining laws then give a whole-cycle isomorphism for arbitrary source
and coefficient gradings. No compatibility of descent with direct sums is
assumed as additional input.

The construction uses the concrete reduced representation, raw graded
cycle and tensor direct-sum dependencies.

-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent

open scoped KasparovDescent

variable {Γ A B E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]

variable (β : CStarAlgebraAction Γ B)

local instance descentGradedSourceSumComplete : CompleteSpace (HilbertModuleSum B E F) :=
  hilbertModuleSum_complete

local instance descentGradedTargetSumComplete : CompleteSpace
    (HilbertModuleSum (ReducedCrossedProduct β) (Module β E) (Module β F)) :=
  hilbertModuleSum_complete

/-- The actual tensor distributivity unitary intertwines the induced
grading for arbitrary coefficient grading. -/
theorem sumModuleEquiv_graded_grading (δB : CStarGrading B)
    (hβ : β.PreservesGrading δB) (J : GradedHilbertModule δB E)
    (K : GradedHilbertModule δB F) (z : Module β (HilbertModuleSum B E F)) :
    sumModuleEquiv β ((moduleGrading β δB hβ (J.sum K)).grading z) =
      ((moduleGrading β δB hβ J).sum (moduleGrading β δB hβ K)).grading
        (sumModuleEquiv β z) :=
  GradedMatrixMoritaTensorDirectSum.hilbertEquiv_grading (coefficientRepresentation β)
    J K (crossedStandardGrading β δB hβ) (coefficientRepresentation_graded β δB hβ) z

variable (α : CStarAlgebraAction Γ A) {δA : CStarGrading A} {δB : CStarGrading B}
  [Countable Γ] [TopologicalSpace.SeparableSpace B]

/-- The actual descended graded cycle of a direct sum is isomorphic to the
direct sum of the actual descended graded cycles through the same complete
coefficient-Hilbert-module unitary in all four intertwining laws. -/
def gradedDirectSumIso (c : GradedKasparovCycle α β δA δB E)
    (d : GradedKasparovCycle α β δA δB F) :
    GradedKasparovCycleIso (gradedCycle β α (c.directSum d))
      ((gradedCycle β α c).directSum (gradedCycle β α d)) where
  moduleEquiv := sumModuleEquiv β
  grading_intertwine := sumModuleEquiv_graded_grading β δB
    c.coefficientAction_preservesGrading c.grading d.grading
  action_intertwine _ _ := rfl
  representation_intertwine := sumModuleEquiv_reducedSourceRepresentation β α
    c.groupAction d.groupAction c.representation d.representation
    c.representation_equivariant d.representation_equivariant
    (c.directSum d).representation_equivariant
  operator_intertwine := sumModuleEquiv_operator β c.operator d.operator

end BC4lean.KKTheory.KasparovDescent
