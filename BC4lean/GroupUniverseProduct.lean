import BC4lean.GradedKasparovProductAssociativity
import BC4lean.GradedKasparovLeftUnitHomotopy
import BC4lean.RightStandardModuleTensorCompatibility
import BC4lean.GradedKasparovSourcePullbackClass
import BC4lean.GradedKasparovFirstSumProduct
import BC4lean.GradedKasparovSecondSumProduct

/-! # Genuine graded products with independent universes

The group, source and three coefficient algebras retain their actual
independent universes. The two actual module universes may also differ;
their completed interior tensor lives in the common maximum. Generic
existence, uniqueness and the actual full interval input witnesses give
the quotient product. Its addition and associativity use the constructed
whole sum unitaries and the actual arbitrary-input triple full witness.
Unit identities are stated in the common module universe containing the
identity coefficient module, without identifying source/coefficient types.
-/

noncomputable section
universe uΓ uA uB uC uD uE uF uG
namespace BC4lean.KKTheory.GroupUniverseProduct

section Pairs
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C] [Countable Γ]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}

def productOperator (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB)
    (d : BundledGradedKasparovCycle.{uΓ, uB, uC, uF} β γ δB δC) :
    AdjointableMap C (InteriorModuleTensor (E := c.carrier) d.cycle.representation)
      (InteriorModuleTensor (E := c.carrier) d.cycle.representation) :=
  Classical.choose (exists_actualGradedKasparovProductOperator c.cycle d.cycle)

theorem productOperator_isProduct
    (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB)
    (d : BundledGradedKasparovCycle.{uΓ, uB, uC, uF} β γ δB δC) :
    IsGradedKasparovProductOperator c.cycle d.cycle (productOperator c d) :=
  Classical.choose_spec (exists_actualGradedKasparovProductOperator c.cycle d.cycle)

def bundledProduct (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB)
    (d : BundledGradedKasparovCycle.{uΓ, uB, uC, uF} β γ δB δC) :
    BundledGradedKasparovCycle.{uΓ, uA, uC, max uE uF} α γ δA δC :=
  BundledGradedKasparovCycle.of (gradedKasparovTensorCycleOfConditions c.cycle d.cycle
    (productOperator c d) (productOperator_isProduct c d).cycleConditions)

theorem bundledProduct_fullHomotopic_first
    {c c' : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}
    (d : BundledGradedKasparovCycle.{uΓ, uB, uC, uF} β γ δB δC)
    (h : c.FullHomotopic c') : (bundledProduct c d).FullHomotopic (bundledProduct c' d) := by
  obtain ⟨h⟩ := h
  exact exists_fullGradedKasparovFirstInputProductHomotopy_of_full d.cycle c.cycle c'.cycle h
    (productOperator_isProduct c d) (productOperator_isProduct c' d)

theorem bundledProduct_fullHomotopic_second
    (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB)
    {d d' : BundledGradedKasparovCycle.{uΓ, uB, uC, uF} β γ δB δC}
    (h : d.FullHomotopic d') : (bundledProduct c d).FullHomotopic (bundledProduct c d') := by
  obtain ⟨h⟩ := h
  exact exists_fullGradedKasparovSecondInputProductHomotopy_of_full c.cycle d.cycle d'.cycle h
    (productOperator_isProduct c d) (productOperator_isProduct c d')

theorem bundledProduct_fullHomotopic
    {c c' : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}
    {d d' : BundledGradedKasparovCycle.{uΓ, uB, uC, uF} β γ δB δC}
    (hc : c.FullHomotopic c') (hd : d.FullHomotopic d') :
    (bundledProduct c d).FullHomotopic (bundledProduct c' d') :=
  BundledGradedKasparovCycle.fullHomotopic_trans
    (bundledProduct_fullHomotopic_first d hc) (bundledProduct_fullHomotopic_second c' hd)

def product : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α β δA δB →
    GradedKasparovHomotopyClass.{uΓ, uB, uC, uF} β γ δB δC →
    GradedKasparovHomotopyClass.{uΓ, uA, uC, max uE uF} α γ δA δC :=
  Quotient.lift₂ (fun c d => GradedKasparovHomotopyClass.mk (bundledProduct c d))
    (fun _ _ _ _ hc hd => Quotient.sound (bundledProduct_fullHomotopic hc hd))

@[simp] theorem product_mk
    (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB)
    (d : BundledGradedKasparovCycle.{uΓ, uB, uC, uF} β γ δB δC) :
    product (GradedKasparovHomotopyClass.mk c) (GradedKasparovHomotopyClass.mk d) =
      GradedKasparovHomotopyClass.mk (bundledProduct c d) := rfl

theorem product_mk_eq_of_isProduct
    (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB)
    (d : BundledGradedKasparovCycle.{uΓ, uB, uC, uF} β γ δB δC)
    {R : AdjointableMap C (InteriorModuleTensor (E := c.carrier) d.cycle.representation)
      (InteriorModuleTensor (E := c.carrier) d.cycle.representation)}
    (hR : IsGradedKasparovProductOperator c.cycle d.cycle R) :
    product (GradedKasparovHomotopyClass.mk c) (GradedKasparovHomotopyClass.mk d) =
      GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
        (gradedKasparovTensorCycleOfConditions c.cycle d.cycle R hR.cycleConditions)) := by
  obtain ⟨h⟩ := exists_fullGradedKasparovProductOperatorHomotopy c.cycle d.cycle
    (productOperator_isProduct c d) hR
  exact Quotient.sound ⟨h⟩

theorem add_product
    (x x' : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α β δA δB)
    (y : GradedKasparovHomotopyClass.{uΓ, uB, uC, uF} β γ δB δC) :
    product (x + x') y = product x y + product x' y := by
  refine Quotient.inductionOn₂ x x' ?_
  intro c c'
  refine Quotient.inductionOn y ?_
  intro d
  have hR := GradedKasparovFirstSumProduct.isProduct c.cycle c'.cycle d.cycle
    (productOperator_isProduct c d) (productOperator_isProduct c' d)
  have hchoice := product_mk_eq_of_isProduct (c.directSum c') d hR
  have hiso := GradedKasparovHomotopyClass.mk_eq_of_iso
    (c := BundledGradedKasparovCycle.of
      (gradedKasparovTensorCycleOfConditions (c.cycle.directSum c'.cycle) d.cycle
        (GradedKasparovFirstSumProduct.operator d.cycle
          (productOperator c d) (productOperator c' d)) hR.cycleConditions))
    (d := (bundledProduct c d).directSum (bundledProduct c' d))
    (GradedKasparovFirstSumProduct.cycleIso c.cycle c'.cycle d.cycle
      (productOperator_isProduct c d) (productOperator_isProduct c' d))
  exact hchoice.trans hiso

theorem product_add
    (x : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α β δA δB)
    (y y' : GradedKasparovHomotopyClass.{uΓ, uB, uC, uF} β γ δB δC) :
    product x (y + y') = product x y + product x y' := by
  refine Quotient.inductionOn x ?_
  intro c
  refine Quotient.inductionOn₂ y y' ?_
  intro d d'
  have hR := GradedKasparovSecondSumProduct.isProduct c.cycle d.cycle d'.cycle
    (productOperator_isProduct c d) (productOperator_isProduct c d')
  have hchoice := product_mk_eq_of_isProduct c (d.directSum d') hR
  have hiso := GradedKasparovHomotopyClass.mk_eq_of_iso
    (c := BundledGradedKasparovCycle.of
      (gradedKasparovTensorCycleOfConditions c.cycle (d.cycle.directSum d'.cycle)
        (GradedKasparovSecondSumProduct.operator d.cycle d'.cycle
          (productOperator c d) (productOperator c d')) hR.cycleConditions))
    (d := (bundledProduct c d).directSum (bundledProduct c d'))
    (GradedKasparovSecondSumProduct.cycleIso c.cycle d.cycle d'.cycle
      (productOperator_isProduct c d) (productOperator_isProduct c d'))
  exact hchoice.trans hiso

end Pairs

section Triples
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} [Group Γ]
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

theorem bundledProduct_fullHomotopic_assoc
    (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB)
    (d : BundledGradedKasparovCycle.{uΓ, uB, uC, uF} β γ δB δC)
    (e : BundledGradedKasparovCycle.{uΓ, uC, uD, uG} γ η δC δD) :
    (bundledProduct (bundledProduct c d) e).FullHomotopic
      (bundledProduct c (bundledProduct d e)) := by
  exact KasparovTriple.exists_fullGradedKasparovAssociativityHomotopy c.cycle d.cycle e.cycle
    (productOperator c d) (productOperator_isProduct c d).cycleConditions
    (productOperator d e) (productOperator_isProduct d e).cycleConditions
    (productOperator c (bundledProduct d e)) (productOperator (bundledProduct c d) e)
    (productOperator_isProduct c d) (productOperator_isProduct d e)
    (productOperator_isProduct (bundledProduct c d) e)
    (productOperator_isProduct c (bundledProduct d e))

theorem product_assoc
    (x : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α β δA δB)
    (y : GradedKasparovHomotopyClass.{uΓ, uB, uC, uF} β γ δB δC)
    (z : GradedKasparovHomotopyClass.{uΓ, uC, uD, uG} γ η δC δD) :
    product (product x y) z = product x (product y z) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro c d e
  exact Quotient.sound (bundledProduct_fullHomotopic_assoc c d e)

end Triples

section Identity
variable {Γ : Type uΓ} {B : Type uB} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]

def identity (β : CStarAlgebraAction Γ B) (δB : CStarGrading B)
    (hβ : β.PreservesGrading δB) :
    GradedKasparovHomotopyClass.{uΓ, uB, uB, uB} β β δB δB :=
  GradedKasparovHomotopyClass.mk
    (BundledGradedKasparovCycle.of (gradedStandardIdentityCycle β δB hβ))

end Identity

section Units
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B] [Countable Γ]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

theorem product_right_identity (hβ : β.PreservesGrading δB)
    (x : GradedKasparovHomotopyClass.{uΓ, uA, uB, max uB uE} α β δA δB) :
    product x (identity β δB hβ) = x := by
  refine Quotient.inductionOn x ?_
  intro c
  obtain ⟨H⟩ := exists_fullGradedKasparovRightUnitHomotopy_of_full c.cycle
    (productOperator_isProduct c
      (BundledGradedKasparovCycle.of (gradedStandardIdentityCycle β δB hβ)))
  exact Quotient.sound ⟨H⟩

theorem product_left_identity [PartialOrder A] [StarOrderedRing A]
    (hα : α.PreservesGrading δA)
    (x : GradedKasparovHomotopyClass.{uΓ, uA, uB, max uA uE} α β δA δB) :
    product (identity α δA hα) x = x := by
  refine Quotient.inductionOn x ?_
  intro c
  obtain ⟨H⟩ := exists_fullGradedKasparovLeftUnitHomotopy_of_full c.cycle
    (productOperator_isProduct
      (BundledGradedKasparovCycle.of (gradedStandardIdentityCycle α δA hα)) c)
  exact Quotient.sound ⟨H⟩

end Units
end BC4lean.KKTheory.GroupUniverseProduct
