import BC4lean.GradedKasparovProductAssociativity
import BC4lean.GradedKasparovProductHomotopyClass

/-! # Associativity on the quotient by actual full interval homotopies

The chosen four genuine products satisfy the previously constructed
arbitrary-input associativity theorem. Its single full interval witness
therefore relates the actual chosen bundled products. Quotient induction
gives associativity for every full graded homotopy class, without selecting
selfadjoint representatives or assuming a common triple product here.
-/

noncomputable section
universe u
namespace BC4lean.KKTheory

variable {Γ A B C D : Type u} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C] [TopologicalSpace.SeparableSpace D] [Countable Γ]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C} {η : CStarAlgebraAction Γ D}
  {δA : CStarGrading A} {δB : CStarGrading B}
  {δC : CStarGrading C} {δD : CStarGrading D}

namespace BundledGradedKasparovCycle

/-- Associativity of the actual chosen bundled products is witnessed by
one full homotopy, retaining both prescribed iterated endpoint cycles. -/
theorem product_fullHomotopic_assoc
    (c : BundledGradedKasparovCycle.{u,u,u,u} α β δA δB)
    (d : BundledGradedKasparovCycle.{u,u,u,u} β γ δB δC)
    (e : BundledGradedKasparovCycle.{u,u,u,u} γ η δC δD) :
    ((c.product d).product e).FullHomotopic (c.product (d.product e)) := by
  exact KasparovTriple.exists_fullGradedKasparovAssociativityHomotopy
    c.cycle d.cycle e.cycle
    (c.productOperator d) (c.productOperator_isProduct d).cycleConditions
    (d.productOperator e) (d.productOperator_isProduct e).cycleConditions
    (c.productOperator (d.product e)) ((c.product d).productOperator e)
    (c.productOperator_isProduct d) (d.productOperator_isProduct e)
    ((c.product d).productOperator_isProduct e) (c.productOperator_isProduct (d.product e))

end BundledGradedKasparovCycle

namespace GradedKasparovHomotopyClass

/-- The genuine product is associative on full graded homotopy classes. -/
theorem product_assoc
    (x : GradedKasparovHomotopyClass.{u,u,u,u} α β δA δB)
    (y : GradedKasparovHomotopyClass.{u,u,u,u} β γ δB δC)
    (z : GradedKasparovHomotopyClass.{u,u,u,u} γ η δC δD) :
    product (product x y) z = product x (product y z) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro c d e
  exact Quotient.sound (BundledGradedKasparovCycle.product_fullHomotopic_assoc c d e)

end GradedKasparovHomotopyClass
end BC4lean.KKTheory
