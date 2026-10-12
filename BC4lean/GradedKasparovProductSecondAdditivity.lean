import BC4lean.GradedKasparovProductFirstAdditivity
import BC4lean.GradedKasparovSecondSumProduct

/-! # Genuine second-variable additivity of the full graded product -/

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

theorem product_add (x : GradedKasparovHomotopyClass.{u,u,u,u} α β δA δB)
    (y y' : GradedKasparovHomotopyClass.{u,u,u,u} β γ δB δC) :
    product x (y + y') = product x y + product x y' := by
  refine Quotient.inductionOn x ?_
  intro c
  refine Quotient.inductionOn₂ y y' ?_
  intro d d'
  have hR := GradedKasparovSecondSumProduct.isProduct c.cycle d.cycle d'.cycle
    (c.productOperator_isProduct d) (c.productOperator_isProduct d')
  have hchoice := product_mk_eq_of_isProduct c (d.directSum d') hR
  have hiso := mk_eq_of_iso
    (c := BundledGradedKasparovCycle.of
      (gradedKasparovTensorCycleOfConditions c.cycle (d.cycle.directSum d'.cycle)
        (GradedKasparovSecondSumProduct.operator d.cycle d'.cycle
          (c.productOperator d) (c.productOperator d')) hR.cycleConditions))
    (d := (c.product d).directSum (c.product d'))
    (GradedKasparovSecondSumProduct.cycleIso c.cycle d.cycle d'.cycle
      (c.productOperator_isProduct d) (c.productOperator_isProduct d'))
  exact hchoice.trans hiso

end BC4lean.KKTheory.GradedKasparovHomotopyClass
