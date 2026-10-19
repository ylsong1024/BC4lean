import BC4lean.KasparovDescentCliffordSignedSource
import BC4lean.KasparovDescentEvenGradedCoherence
import BC4lean.GradedKasparovSourcePullback

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Whole graded-cycle signed-source descent coherence

Both endpoint cycles are built from actual cycle
constructors. The source crossed algebra is identified using the actual
pair crossed-product equivalence, and the only coefficient regrading is
the proved equality of the crossed trivial grading with the trivial grading.
The same tensor-sum unitary intertwines all four pieces of cycle data.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent

variable {Γ A B E : Type*} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  (β : CStarAlgebraAction Γ B) (α : CStarAlgebraAction Γ A)

local instance signedSourceIsoSumComplete : CompleteSpace (HilbertModuleSum B E E) :=
  hilbertModuleSum_complete
local instance signedSourceIsoTargetComplete : CompleteSpace
    (HilbertModuleSum (ReducedCrossedProduct β) (Module β E) (Module β E)) :=
  hilbertModuleSum_complete

/-- Descend the actual signed odd-source cycle and identify its genuinely
trivial crossed coefficient grading by equality transport. -/
def descendedSignedSource (c : OddKasparovCycle α β E) :=
  (gradedCycle β (cliffordCoefficientAction α) (CliffordOddSourceCycle.cycle c)).regrade
    rfl (reducedCrossedProductGrading_trivial β)

/-- First descend the actual odd cycle, then form its signed source and
pull its actual source representation back through the actual crossed pair iso. -/
def signedSourceOfDescent (c : OddKasparovCycle α β E) :=
  (CliffordOddSourceCycle.cycle (oddCycle β α c)).sourcePullback
    (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
      (ReducedCrossedProduct (cliffordCoefficientAction α)))
    (reducedCrossedProductGrading (cliffordCoefficientAction α) cliffordCoefficientGrading
      (cliffordCoefficientAction_preservesGrading α))
    (fun _ _ => rfl) (ReducedCrossedProductPair.equiv α).toNonUnitalStarAlgHom
    (fun _ _ => rfl) (ReducedCrossedProductPair.equiv_grading α)

private theorem signedSourceDescentIso_grading_aux
    (c : OddKasparovCycle α β E) (z : Module β (HilbertModuleSum B E E)) :
    sumModuleEquiv (E := E) (F := E) β
        ((descendedSignedSource β α c).grading.grading z) =
      (signedSourceOfDescent β α c).grading.grading
        (sumModuleEquiv (E := E) (F := E) β z) := by
  have h₁ := congrArg
    (fun v : Module β (HilbertModuleSum B E E) =>
      sumModuleEquiv (E := E) (F := E) β v)
    (GradedKasparovCycle.regrade_grading_apply
      (Γ := Unit) (A := ReducedCrossedProduct (cliffordCoefficientAction α))
      (B := ReducedCrossedProduct β) (E := Module β (HilbertModuleSum B E E))
      (gradedCycle (E := HilbertModuleSum B E E) β (cliffordCoefficientAction α)
        (CliffordOddSourceCycle.cycle c))
      rfl (reducedCrossedProductGrading_trivial (Γ := Γ) (B := B) β) z)
  have h₂ := congrArg
    (fun v : Module β (HilbertModuleSum B E E) =>
      sumModuleEquiv (E := E) (F := E) β v)
    (moduleGrading_trivial_apply (Γ := Γ) (B := B) (E := HilbertModuleSum B E E) β
      (CliffordOddSourceCycle.grading (C := B) (H := E)) z)
  have h₃ := sumModuleEquiv_signedSource_grading (Γ := Γ) (B := B) (E := E) β z
  exact h₁.trans (h₂.trans h₃)

private theorem signedSourceDescentIso_action_aux
    (c : OddKasparovCycle α β E) (g : Unit)
    (z : Module β (HilbertModuleSum B E E)) :
    sumModuleEquiv (E := E) (F := E) β
        ((descendedSignedSource β α c).groupAction.action g z) =
      (signedSourceOfDescent β α c).groupAction.action g
        (sumModuleEquiv (E := E) (F := E) β z) := by
  have hg : g = (1 : Unit) := Subsingleton.elim _ _
  have hsource : (descendedSignedSource β α c).groupAction.action g z = z :=
    (congrArg
      (fun k : Unit => (descendedSignedSource β α c).groupAction.action k z) hg).trans
      (EquivariantHilbertModule.one_apply
        (descendedSignedSource β α c).groupAction z)
  have htarget :
      (signedSourceOfDescent β α c).groupAction.action g
          (sumModuleEquiv (E := E) (F := E) β z) =
        sumModuleEquiv (E := E) (F := E) β z :=
    (congrArg
      (fun k : Unit => (signedSourceOfDescent β α c).groupAction.action k
        (sumModuleEquiv (E := E) (F := E) β z)) hg).trans
      (EquivariantHilbertModule.one_apply
        (signedSourceOfDescent β α c).groupAction (sumModuleEquiv (E := E) (F := E) β z))
  exact (congrArg
    (fun v : Module β (HilbertModuleSum B E E) =>
      sumModuleEquiv (E := E) (F := E) β v) hsource).trans htarget.symm

private theorem signedSourceDescentIso_representation_aux
    (c : OddKasparovCycle α β E)
    (a : ReducedCrossedProduct (cliffordCoefficientAction α))
    (z : Module β (HilbertModuleSum B E E)) :
    sumModuleEquiv (E := E) (F := E) β
        ((descendedSignedSource β α c).representation a z) =
      (signedSourceOfDescent β α c).representation a
        (sumModuleEquiv (E := E) (F := E) β z) := by
  have h₁ := congrArg
    (fun ρ : ReducedCrossedProduct (cliffordCoefficientAction α) →⋆ₙₐ[ℂ]
      AdjointableMap (ReducedCrossedProduct β) (Module β (HilbertModuleSum B E E))
        (Module β (HilbertModuleSum B E E)) =>
      sumModuleEquiv (E := E) (F := E) β (ρ a z))
    (GradedKasparovCycle.regrade_representation
      (Γ := Unit) (A := ReducedCrossedProduct (cliffordCoefficientAction α))
      (B := ReducedCrossedProduct β) (E := Module β (HilbertModuleSum B E E))
      (gradedCycle (E := HilbertModuleSum B E E) β (cliffordCoefficientAction α)
        (CliffordOddSourceCycle.cycle c))
      rfl (reducedCrossedProductGrading_trivial (Γ := Γ) (B := B) β))
  have h₂ := sumModuleEquiv_signedSource_representation (Γ := Γ) (A := A) (B := B)
    (E := E) β α c.groupAction c.representation c.representation_equivariant a z
  exact h₁.trans h₂

private theorem signedSourceDescentIso_operator_aux
    (c : OddKasparovCycle α β E) (z : Module β (HilbertModuleSum B E E)) :
    sumModuleEquiv (E := E) (F := E) β ((descendedSignedSource β α c).operator z) =
      (signedSourceOfDescent β α c).operator (sumModuleEquiv (E := E) (F := E) β z) := by
  have h₁ := congrArg
    (fun T : AdjointableMap (ReducedCrossedProduct β) (Module β (HilbertModuleSum B E E))
      (Module β (HilbertModuleSum B E E)) =>
      sumModuleEquiv (E := E) (F := E) β (T z))
    (GradedKasparovCycle.regrade_operator
      (Γ := Unit) (A := ReducedCrossedProduct (cliffordCoefficientAction α))
      (B := ReducedCrossedProduct β) (E := Module β (HilbertModuleSum B E E))
      (gradedCycle (E := HilbertModuleSum B E E) β (cliffordCoefficientAction α)
        (CliffordOddSourceCycle.cycle c))
      rfl (reducedCrossedProductGrading_trivial (Γ := Γ) (B := B) β))
  have h₂ := sumModuleEquiv_signedSource_operator (Γ := Γ) (B := B) (E := E) β c.operator z
  exact h₁.trans h₂

/-- Actual whole-cycle coherence for the signed-source Clifford model. -/
def signedSourceDescentIso (c : OddKasparovCycle α β E) :
    GradedKasparovCycleIso (descendedSignedSource β α c) (signedSourceOfDescent β α c) where
  moduleEquiv := sumModuleEquiv β
  grading_intertwine z := signedSourceDescentIso_grading_aux (E := E) β α c z
  action_intertwine g z := signedSourceDescentIso_action_aux (E := E) β α c g z
  representation_intertwine a z :=
    signedSourceDescentIso_representation_aux (E := E) β α c a z
  operator_intertwine z := signedSourceDescentIso_operator_aux (E := E) β α c z

end BC4lean.KKTheory.KasparovDescent
