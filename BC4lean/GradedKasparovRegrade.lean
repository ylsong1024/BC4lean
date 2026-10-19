import BC4lean.GroupUniverseProduct

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Changing only provably equal grading indices

Every map here is equality transport.
There is no hypothesis relating different gradings, no altered cycle data,
and no change to the actual full-homotopy quotient relation.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A B C E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  {δA δA' : CStarGrading A} {δB δB' : CStarGrading B} {δC δC' : CStarGrading C}

/-- Transport the actual raw cycle along equalities of its two grading indices. -/
def GradedKasparovCycle.regrade (c : GradedKasparovCycle α β δA δB E)
    (hA : δA = δA') (hB : δB = δB') : GradedKasparovCycle α β δA' δB' E := by
  subst δA'; subst δB'; exact c

@[simp] theorem GradedKasparovCycle.regrade_grading_apply
    (c : GradedKasparovCycle α β δA δB E) (hA : δA = δA') (hB : δB = δB') (x : E) :
    (c.regrade hA hB).grading.grading x = c.grading.grading x := by
  subst δA'; subst δB'; rfl

@[simp] theorem GradedKasparovCycle.regrade_representation
    (c : GradedKasparovCycle α β δA δB E) (hA : δA = δA') (hB : δB = δB') :
    (c.regrade hA hB).representation = c.representation := by
  subst δA'; subst δB'; rfl

@[simp] theorem GradedKasparovCycle.regrade_operator
    (c : GradedKasparovCycle α β δA δB E) (hA : δA = δA') (hB : δB = δB') :
    (c.regrade hA hB).operator = c.operator := by
  subst δA'; subst δB'; rfl

@[simp] theorem GradedKasparovCycle.regrade_action
    (c : GradedKasparovCycle α β δA δB E) (hA : δA = δA') (hB : δB = δB') :
    (c.regrade hA hB).groupAction = c.groupAction := by
  subst δA'; subst δB'; rfl

end BC4lean.KKTheory

universe uΓ uA uB uC uE uF
namespace BC4lean.KKTheory.GradedKasparovHomotopyClass

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  {δA δA' : CStarGrading A} {δB δB' : CStarGrading B} {δC δC' : CStarGrading C}

/-- Equality transport of the actual full-homotopy quotient. -/
def regrade (hA : δA = δA') (hB : δB = δB') :
    GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β δA δB →
    GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β δA' δB' := by
  subst δA'; subst δB'; exact id

@[simp] theorem regrade_mk (hA : δA = δA') (hB : δB = δB')
    (c : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA δB) :
    regrade hA hB (mk c) = mk (BundledGradedKasparovCycle.of (c.cycle.regrade hA hB)) := by
  subst δA'; subst δB'
  change mk c = mk (BundledGradedKasparovCycle.of c.cycle)
  exact congrArg mk (BundledGradedKasparovCycle.of_storedCycle c).symm

variable [TopologicalSpace.SeparableSpace A]
  [TopologicalSpace.SeparableSpace C] [Countable Γ]

/-- The existing genuine product commutes with equality transport of grading
indices, proved by equality induction rather than a compatibility assumption. -/
theorem regrade_product (hA : δA = δA') (hB : δB = δB') (hC : δC = δC')
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β δA δB)
    (y : GradedKasparovHomotopyClass.{uΓ,uB,uC,uF} β γ δB δC) :
    regrade hA hC (GroupUniverseProduct.product x y) =
      GroupUniverseProduct.product (regrade hA hB x) (regrade hB hC y) := by
  subst δA'; subst δB'; subst δC'; rfl

end BC4lean.KKTheory.GradedKasparovHomotopyClass
