import BC4lean.GroupUniverseProduct
import BC4lean.GradedKasparovCoefficientProduct
import BC4lean.FullGradedCoefficientTransport
import BC4lean.GradedKasparovSourcePullbackFunctoriality

/-! # Actual product transport through independent coefficient equivalences

An invertible coefficient change retains the actual module carrier and
transports its full coefficient-valued inner product and arbitrary full
interval witness. The real changed tensor unitary transports every product
condition. Whole identity coefficient and source units then give final
coefficient naturality without identifying any coefficient universes.
-/

noncomputable section
universe uΓ uA uB uB' uC uC' uE uF
namespace BC4lean.KKTheory.GroupUniverseProductCoefficientEquivalence

section ClassMap
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {B' : Type uB'} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra B'] [PartialOrder B'] [StarOrderedRing B']
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace B']
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {β' : CStarAlgebraAction Γ B'}
  {δA : CStarGrading A} {δB : CStarGrading B} {δB' : CStarGrading B'}

def changeCoefficients (e : GradedCoefficientEquiv β δB β' δB') :
    GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β δA δB →
    GradedKasparovHomotopyClass.{uΓ,uA,uB',uE} α β' δA δB' :=
  Quotient.lift (fun c => GradedKasparovHomotopyClass.mk (c.changeCoefficients e)) (by
    intro c d h
    obtain ⟨h⟩ := h
    exact Quotient.sound ⟨h.changeCoefficients e⟩)

@[simp] theorem changeCoefficients_mk (e : GradedCoefficientEquiv β δB β' δB')
    (c : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA δB) :
    changeCoefficients e (GradedKasparovHomotopyClass.mk c) =
      GradedKasparovHomotopyClass.mk (c.changeCoefficients e) := rfl

def identityEquiv (β : CStarAlgebraAction Γ B) (δB : CStarGrading B) :
    GradedCoefficientEquiv β δB β δB where
  starAlgEquiv := StarAlgEquiv.refl ℂ B
  action_intertwine _ _ := rfl
  grading_intertwine _ := rfl

def identityCycleIso
    (c : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA δB) :
    GradedKasparovCycleIso (c.changeCoefficients (identityEquiv β δB)).cycle c.cycle where
  moduleEquiv :=
    { linearIsometryEquiv :=
        { toFun := id
          invFun := id
          left_inv _ := rfl
          right_inv _ := rfl
          map_add' _ _ := rfl
          map_smul' _ _ := rfl
          norm_map' _ := rfl }
      inner_map _ _ := rfl }
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

theorem changeCoefficients_identity
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β δA δB) :
    changeCoefficients (identityEquiv β δB) x = x := by
  refine Quotient.inductionOn x ?_
  intro c
  exact GradedKasparovHomotopyClass.mk_eq_of_iso (identityCycleIso c)

end ClassMap

section Product
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {B' : Type uB'}
  {C : Type uC} {C' : Type uC'} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra B'] [PartialOrder B'] [StarOrderedRing B']
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NonUnitalCStarAlgebra C'] [PartialOrder C'] [StarOrderedRing C']
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace B'] [TopologicalSpace.SeparableSpace C]
  [TopologicalSpace.SeparableSpace C'] [Countable Γ]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {β' : CStarAlgebraAction Γ B'}
  {γ : CStarAlgebraAction Γ C} {γ' : CStarAlgebraAction Γ C'}
  {δA : CStarGrading A} {δB : CStarGrading B} {δB' : CStarGrading B'}
  {δC : CStarGrading C} {δC' : CStarGrading C'}

def secondCoefficientInput (eB : GradedCoefficientEquiv β δB β' δB')
    (eC : GradedCoefficientEquiv γ δC γ' δC') (hβ : β.PreservesGrading δB)
    (y : GradedKasparovHomotopyClass.{uΓ,uB,uC,uF} β γ δB δC) :
    GradedKasparovHomotopyClass.{uΓ,uB',uC',uF} β' γ' δB' δC' :=
  changeCoefficients eC (GradedKasparovHomotopyClass.sourcePullback β' δB'
    (eB.preservesGrading hβ) eB.symm.starAlgEquiv.toNonUnitalStarAlgHom
    eB.symm.action_intertwine eB.symm.grading_intertwine y)

set_option maxHeartbeats 2000000 in
theorem changeCoefficients_product (eB : GradedCoefficientEquiv β δB β' δB')
    (eC : GradedCoefficientEquiv γ δC γ' δC') (hβ : β.PreservesGrading δB)
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β δA δB)
    (y : GradedKasparovHomotopyClass.{uΓ,uB,uC,uF} β γ δB δC) :
    changeCoefficients eC (GroupUniverseProduct.product x y) =
      GroupUniverseProduct.product (changeCoefficients eB x) (secondCoefficientInput eB eC hβ y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro c d
  let c' := BundledGradedKasparovCycle.of (GradedKasparovCoefficientTensorInputs.first eB c.cycle)
  let d' := BundledGradedKasparovCycle.of (GradedKasparovCoefficientTensorInputs.second eB eC d.cycle)
  have hR := GradedKasparovCoefficientProduct.isProduct eB eC c.cycle d.cycle
    (GroupUniverseProduct.productOperator_isProduct c d)
  have hright := GroupUniverseProduct.product_mk_eq_of_isProduct c' d' hR
  have hiso := GradedKasparovHomotopyClass.mk_eq_of_iso
    (c := (GroupUniverseProduct.bundledProduct c d).changeCoefficients eC)
    (d := BundledGradedKasparovCycle.of
      (gradedKasparovTensorCycleOfConditions
        (GradedKasparovCoefficientTensorInputs.first eB c.cycle)
        (GradedKasparovCoefficientTensorInputs.second eB eC d.cycle)
        (GradedKasparovCoefficientProduct.operator eB eC d.cycle
          (GroupUniverseProduct.productOperator c d)) hR.cycleConditions))
    (GradedKasparovCoefficientProduct.cycleIso eB eC c.cycle d.cycle
      (GroupUniverseProduct.productOperator_isProduct c d))
  exact hiso.trans hright.symm

theorem changeFinalCoefficients_product (eC : GradedCoefficientEquiv γ δC γ' δC')
    (hβ : β.PreservesGrading δB)
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β δA δB)
    (y : GradedKasparovHomotopyClass.{uΓ,uB,uC,uF} β γ δB δC) :
    changeCoefficients eC (GroupUniverseProduct.product x y) =
      GroupUniverseProduct.product x (changeCoefficients eC y) := by
  have h := changeCoefficients_product (identityEquiv β δB) eC hβ x y
  have hy : secondCoefficientInput (identityEquiv β δB) eC hβ y = changeCoefficients eC y := by
    unfold secondCoefficientInput
    congr 1
    exact GradedKasparovHomotopyClass.sourcePullback_id hβ y
  simpa only [changeCoefficients_identity, hy] using h

end Product
end BC4lean.KKTheory.GroupUniverseProductCoefficientEquivalence
