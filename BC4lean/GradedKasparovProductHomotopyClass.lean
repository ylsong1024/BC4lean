import BC4lean.GradedKasparovFirstInputProductHomotopy
import BC4lean.GradedKasparovSecondInputProductHomotopy
import BC4lean.GradedKasparovLeftUnitHomotopy
import BC4lean.RightStandardModuleTensorCompatibility
import BC4lean.GradedKasparovSourcePullbackClass

/-! # The actual product on full graded homotopy classes

Product operators are chosen from the constructed generic existence theorem.
Actual uniqueness removes this choice; actual products on arbitrary interval
input modules prove independence in both variables. Thus the binary map
descends to the quotient by one full witness. Both unit laws use the genuine
full witnesses, including the nonunital ideal construction for the left unit.
-/

noncomputable section
universe u
namespace BC4lean.KKTheory

variable {Γ A B C : Type u} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C] [Countable Γ]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}

namespace BundledGradedKasparovCycle
variable (c : BundledGradedKasparovCycle.{u,u,u,u} α β δA δB)
  (d : BundledGradedKasparovCycle.{u,u,u,u} β γ δB δC)

def productOperator : AdjointableMap C (InteriorModuleTensor (E := c.carrier) d.cycle.representation)
    (InteriorModuleTensor (E := c.carrier) d.cycle.representation) :=
  Classical.choose (exists_actualGradedKasparovProductOperator c.cycle d.cycle)

theorem productOperator_isProduct : IsGradedKasparovProductOperator c.cycle d.cycle
    (c.productOperator d) :=
  Classical.choose_spec (exists_actualGradedKasparovProductOperator c.cycle d.cycle)

def product : BundledGradedKasparovCycle.{u,u,u,u} α γ δA δC :=
  of (gradedKasparovTensorCycleOfConditions c.cycle d.cycle (c.productOperator d)
    (c.productOperator_isProduct d).cycleConditions)

theorem product_fullHomotopic_of_first {c c' : BundledGradedKasparovCycle.{u,u,u,u} α β δA δB}
    (h : c.FullHomotopic c') : (c.product d).FullHomotopic (c'.product d) := by
  obtain ⟨h⟩ := h
  exact exists_fullGradedKasparovFirstInputProductHomotopy_of_full d.cycle c.cycle c'.cycle h
    (c.productOperator_isProduct d) (c'.productOperator_isProduct d)

theorem product_fullHomotopic_of_second {d d' : BundledGradedKasparovCycle.{u,u,u,u} β γ δB δC}
    (h : d.FullHomotopic d') : (c.product d).FullHomotopic (c.product d') := by
  obtain ⟨h⟩ := h
  exact exists_fullGradedKasparovSecondInputProductHomotopy_of_full c.cycle d.cycle d'.cycle h
    (c.productOperator_isProduct d) (c.productOperator_isProduct d')

theorem product_fullHomotopic
    {c c' : BundledGradedKasparovCycle.{u,u,u,u} α β δA δB}
    {d d' : BundledGradedKasparovCycle.{u,u,u,u} β γ δB δC}
    (hc : c.FullHomotopic c') (hd : d.FullHomotopic d') :
    (c.product d).FullHomotopic (c'.product d') :=
  fullHomotopic_trans (product_fullHomotopic_of_first d hc)
    (product_fullHomotopic_of_second c' hd)

end BundledGradedKasparovCycle

namespace GradedKasparovHomotopyClass

def product : GradedKasparovHomotopyClass.{u,u,u,u} α β δA δB →
    GradedKasparovHomotopyClass.{u,u,u,u} β γ δB δC →
    GradedKasparovHomotopyClass.{u,u,u,u} α γ δA δC :=
  Quotient.lift₂ (fun c d => mk (c.product d))
    (fun _ _ _ _ hc hd => Quotient.sound (BundledGradedKasparovCycle.product_fullHomotopic hc hd))

@[simp] theorem product_mk (c : BundledGradedKasparovCycle.{u,u,u,u} α β δA δB)
    (d : BundledGradedKasparovCycle.{u,u,u,u} β γ δB δC) :
    product (mk c) (mk d) = mk (c.product d) := rfl

/-- Every actual product representative defines the same product class. -/
theorem product_mk_eq_of_isProduct
    (c : BundledGradedKasparovCycle.{u,u,u,u} α β δA δB)
    (d : BundledGradedKasparovCycle.{u,u,u,u} β γ δB δC)
    {R : AdjointableMap C (InteriorModuleTensor (E := c.carrier) d.cycle.representation)
      (InteriorModuleTensor (E := c.carrier) d.cycle.representation)}
    (hR : IsGradedKasparovProductOperator c.cycle d.cycle R) :
    product (mk c) (mk d) = mk (BundledGradedKasparovCycle.of
      (gradedKasparovTensorCycleOfConditions c.cycle d.cycle R hR.cycleConditions)) := by
  obtain ⟨h⟩ := exists_fullGradedKasparovProductOperatorHomotopy c.cycle d.cycle
    (c.productOperator_isProduct d) hR
  exact Quotient.sound ⟨h⟩

def identity (β : CStarAlgebraAction Γ B) (δB : CStarGrading B)
    (hβ : β.PreservesGrading δB) : GradedKasparovHomotopyClass.{u,u,u,u} β β δB δB :=
  mk (BundledGradedKasparovCycle.of (gradedStandardIdentityCycle β δB hβ))

theorem product_right_identity (hβ : β.PreservesGrading δB)
    (x : GradedKasparovHomotopyClass.{u,u,u,u} α β δA δB) :
    product x (identity β δB hβ) = x := by
  refine Quotient.inductionOn x ?_
  intro c
  obtain ⟨H⟩ := exists_fullGradedKasparovRightUnitHomotopy_of_full c.cycle
    (c.productOperator_isProduct (BundledGradedKasparovCycle.of (gradedStandardIdentityCycle β δB hβ)))
  exact Quotient.sound ⟨H⟩

theorem product_left_identity [PartialOrder A] [StarOrderedRing A]
    (hα : α.PreservesGrading δA)
    (x : GradedKasparovHomotopyClass.{u,u,u,u} α β δA δB) :
    product (identity α δA hα) x = x := by
  refine Quotient.inductionOn x ?_
  intro c
  obtain ⟨H⟩ := exists_fullGradedKasparovLeftUnitHomotopy_of_full c.cycle
    ((BundledGradedKasparovCycle.of (gradedStandardIdentityCycle α δA hα)).productOperator_isProduct c)
  exact Quotient.sound ⟨H⟩

end GradedKasparovHomotopyClass
end BC4lean.KKTheory
