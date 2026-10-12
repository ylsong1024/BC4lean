import BC4lean.GradedKasparovProductHomotopyClass
import BC4lean.GradedKasparovFirstSumProduct

/-! # Genuine first-variable additivity of the full graded product -/

noncomputable section
universe u
namespace BC4lean.KKTheory.GradedKasparovHomotopyClass

variable {Γ A B C : Type u} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C] [Countable Γ]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}

theorem add_product (x x' : GradedKasparovHomotopyClass.{u,u,u,u} α β δA δB)
    (y : GradedKasparovHomotopyClass.{u,u,u,u} β γ δB δC) :
    product (x + x') y = product x y + product x' y := by
  refine Quotient.inductionOn₂ x x' ?_
  intro c c'
  refine Quotient.inductionOn y ?_
  intro d
  have hR := GradedKasparovFirstSumProduct.isProduct c.cycle c'.cycle d.cycle
    (c.productOperator_isProduct d) (c'.productOperator_isProduct d)
  have hchoice := product_mk_eq_of_isProduct (c.directSum c') d hR
  have hiso := mk_eq_of_iso
    (c := BundledGradedKasparovCycle.of
      (gradedKasparovTensorCycleOfConditions (c.cycle.directSum c'.cycle) d.cycle
        (GradedKasparovFirstSumProduct.operator d.cycle
          (c.productOperator d) (c'.productOperator d)) hR.cycleConditions))
    (d := (c.product d).directSum (c'.product d))
    (GradedKasparovFirstSumProduct.cycleIso c.cycle c'.cycle d.cycle
      (c.productOperator_isProduct d) (c'.productOperator_isProduct d))
  exact hchoice.trans hiso

end BC4lean.KKTheory.GradedKasparovHomotopyClass
