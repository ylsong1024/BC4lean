import BC4lean.KasparovDescentGradedIntervalCycle
import BC4lean.KasparovDescentGradedCycleIso
import BC4lean.KasparovDescentIntervalFibreIso
import BC4lean.FullGradedKasparovHomotopy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Genuine fully graded full interval homotopy transport

The construction uses the norm-bridge and cycle results.
 This constructs a full target interval witness
on the actual arbitrary coefficient-extension module, with whole-cycle
endpoint unitaries and both actual induced crossed algebra gradings.
No product comparison, quotient map, or parity compatibility is claimed.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent CStarAlgebra

section Fibre
variable {Γ A B X : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  (β : CStarAlgebraAction Γ B) (M : Type*)
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M]
  [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]
  (α : CStarAlgebraAction Γ A) {δA : CStarGrading A} {δB : CStarGrading B}
  [Countable Γ] [TopologicalSpace.SeparableSpace B]

/-- The same actual fibre tensor unitary intertwines the whole graded cycle. -/
def intervalGradedCycleFibreIso (hβ : β.PreservesGrading δB)
    (c : GradedKasparovCycle α (β.continuousSections (X := X)) δA δB.continuousSections M)
    (t : X) :
    GradedKasparovCycleIso ((intervalGradedCycle β M α hβ c).fibre t)
      (gradedCycle β α (c.fibre t)) where
  moduleEquiv := intervalFibreEquiv β M t
  grading_intertwine := intervalFibreEquiv_gradedGrading β M δB hβ t c.grading
  action_intertwine := intervalFibreEquiv_targetAction β M t
  representation_intertwine := intervalFibreEquiv_reducedSourceRepresentation β M α
    c.groupAction c.representation c.representation_equivariant t
  operator_intertwine := intervalFibreEquiv_operator β M t c.operator

end Fibre

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]
  (β : CStarAlgebraAction Γ B) (α : CStarAlgebraAction Γ A)
  {δA : CStarGrading A} {δB : CStarGrading B}

/-- The genuine fully graded raw cycle, bundled in its actual enlarged universe. -/
def bundledGradedCycle (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB) :
    BundledGradedKasparovCycle.{0, max uΓ uA, max uΓ uB, max uE (max uΓ uB)}
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β))
      (reducedCrossedProductGrading α δA c.cycle.sourceAction_preservesGrading)
      (reducedCrossedProductGrading β δB c.cycle.coefficientAction_preservesGrading) :=
  BundledGradedKasparovCycle.of (gradedCycle β α c.cycle)

/-- Every genuine fully graded arbitrary interval witness has a genuine full
descended witness, with no fixed-module path replacement. -/
def gradedFullHomotopy
    {c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}
    (h : FullGradedKasparovHomotopy c d) :
    FullGradedKasparovHomotopy (bundledGradedCycle β α c) (bundledGradedCycle β α d) where
  intervalCycle := BundledGradedKasparovCycle.of
    (intervalGradedCycle β h.intervalCycle.carrier α c.cycle.coefficientAction_preservesGrading
      h.intervalCycle.cycle)
  sourceIso := (intervalGradedCycleFibreIso β h.intervalCycle.carrier α
    c.cycle.coefficientAction_preservesGrading h.intervalCycle.cycle 0).trans
      (gradedCycleIso β α h.sourceIso)
  targetIso := (intervalGradedCycleFibreIso β h.intervalCycle.carrier α
    c.cycle.coefficientAction_preservesGrading h.intervalCycle.cycle 1).trans
      (gradedCycleIso β α h.targetIso)

end BC4lean.KKTheory.KasparovDescent
