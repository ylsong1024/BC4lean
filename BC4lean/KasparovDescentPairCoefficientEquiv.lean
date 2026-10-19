import BC4lean.ReducedCrossedProductPair
import BC4lean.GroupUniverseProductCoefficientEquivalence
import BC4lean.GroupUniverseProductSource

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual graded Clifford coefficient change after reduced descent

The pair equivalence is packaged with the actual target group `Unit`, the
actual induced grading on the crossed coefficient algebra, and the existing
coordinate Clifford action and grading. Its action compatibility is proved
because both target actions act identically on every element.

The class maps below reuse the existing quotient by one full arbitrary-module
interval homotopy witness. In particular coefficient change transports that
whole witness; no fixed-module operator-path quotient is substituted. Source
pullback uses the inverse pair equivalence. The three product identities are
specializations of the existing genuine graded product transport theorems.

These transport identities are inputs to native EO, OE and OO descent
compatibility. They do not identify native parity constructions with descended
graded representatives; those whole-cycle comparisons are separate results.


-/

noncomputable section
universe uΓ uB uA uC uD uE uF
namespace BC4lean.KKTheory.KasparovDescentPairCoefficientEquiv
open scoped KasparovDescent CStarAlgebra

variable {Γ : Type uΓ} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The ordinary target action on the actual crossed Clifford algebra. -/
abbrev sourceAction (β : CStarAlgebraAction Γ B) :
    CStarAlgebraAction Unit (ReducedCrossedProduct (cliffordCoefficientAction β)) :=
  CStarAlgebraAction.trivial

/-- The grading obtained from the original coefficient swap by actual regular
Hilbert-module conjugation and restriction to the closed crossed algebra. -/
abbrev sourceGrading (β : CStarAlgebraAction Γ B) :
    CStarGrading (ReducedCrossedProduct (cliffordCoefficientAction β)) :=
  reducedCrossedProductGrading (cliffordCoefficientAction β)
    cliffordCoefficientGrading (cliffordCoefficientAction_preservesGrading β)

/-- The existing Clifford action on the pair of ordinary crossed coefficients. -/
abbrev targetAction (β : CStarAlgebraAction Γ B) :
    CStarAlgebraAction Unit (ReducedCrossedProduct β × ReducedCrossedProduct β) :=
  cliffordCoefficientAction
    (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β))

/-- The existing coordinate-swap grading, with no new grading structure. -/
abbrev targetGrading (β : CStarAlgebraAction Γ B) :
    CStarGrading (ReducedCrossedProduct β × ReducedCrossedProduct β) :=
  cliffordCoefficientGrading

@[simp] theorem sourceAction_apply (β : CStarAlgebraAction Γ B) (g : Unit)
    (c : ReducedCrossedProduct (cliffordCoefficientAction β)) :
    (sourceAction β).automorphism g c = c := rfl

@[simp] theorem targetAction_apply (β : CStarAlgebraAction Γ B) (g : Unit)
    (c : ReducedCrossedProduct β × ReducedCrossedProduct β) :
    (targetAction β).automorphism g c = c := by
  cases c
  rfl

theorem sourceAction_preservesGrading (β : CStarAlgebraAction Γ B) :
    (sourceAction β).PreservesGrading (sourceGrading β) := fun _ _ => rfl

theorem targetAction_preservesGrading (β : CStarAlgebraAction Γ B) :
    (targetAction β).PreservesGrading (targetGrading β) :=
  cliffordCoefficientAction_preservesGrading _

/-- The actual coefficient equivalence needed by the existing full graded
coefficient-change, source-pullback, and genuine product APIs. -/
def equiv (β : CStarAlgebraAction Γ B) :
    GradedCoefficientEquiv (sourceAction β) (sourceGrading β)
      (targetAction β) (targetGrading β) where
  starAlgEquiv := ReducedCrossedProductPair.equiv β
  action_intertwine g c := by
    rw [sourceAction_apply, targetAction_apply]
  grading_intertwine := ReducedCrossedProductPair.equiv_grading β

@[simp] theorem equiv_starAlgEquiv (β : CStarAlgebraAction Γ B) :
    (equiv β).starAlgEquiv = ReducedCrossedProductPair.equiv β := rfl

@[simp] theorem equiv_coefficient (β : CStarAlgebraAction Γ B) (b : B × B) :
    (equiv β).starAlgEquiv (coefficientToReducedCrossed (cliffordCoefficientAction β) b) =
      (coefficientToReducedCrossed β b.1, coefficientToReducedCrossed β b.2) :=
  ReducedCrossedProductPair.equiv_coefficient β b

section Classes
variable [Countable Γ] [TopologicalSpace.SeparableSpace B]

variable {A : Type uA} [NonUnitalCStarAlgebra A]
  {α : CStarAlgebraAction Unit A} {δA : CStarGrading A}

/-- Actual change of the final crossed Clifford coefficient algebra on the
quotient by one full arbitrary-module homotopy witness. -/
def changeCoefficients (β : CStarAlgebraAction Γ B)
    (x : GradedKasparovHomotopyClass.{0,uA,max uΓ uB,uE}
      α (sourceAction β) δA (sourceGrading β)) :
    GradedKasparovHomotopyClass.{0,uA,max uΓ uB,uE}
      α (targetAction β) δA (targetGrading β) :=
  GroupUniverseProductCoefficientEquivalence.changeCoefficients (equiv β) x

@[simp] theorem changeCoefficients_mk (β : CStarAlgebraAction Γ B)
    (c : BundledGradedKasparovCycle.{0,uA,max uΓ uB,uE}
      α (sourceAction β) δA (sourceGrading β)) :
    changeCoefficients β (GradedKasparovHomotopyClass.mk c) =
      GradedKasparovHomotopyClass.mk (c.changeCoefficients (equiv β)) := rfl

variable {C : Type uC} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace C]
  {η : CStarAlgebraAction Unit C} {δC : CStarGrading C}

/-- Actual source change from the crossed Clifford algebra to the coordinate
pair, by precomposing with the constructed inverse pair equivalence. -/
def sourcePullback (β : CStarAlgebraAction Γ B)
    (y : GradedKasparovHomotopyClass.{0,max uΓ uB,uC,uF}
      (sourceAction β) η (sourceGrading β) δC) :
    GradedKasparovHomotopyClass.{0,max uΓ uB,uC,uF}
      (targetAction β) η (targetGrading β) δC :=
  GradedKasparovHomotopyClass.sourcePullback
    (targetAction β) (targetGrading β) (targetAction_preservesGrading β)
    (equiv β).symm.starAlgEquiv.toNonUnitalStarAlgHom
    (equiv β).symm.action_intertwine (equiv β).symm.grading_intertwine y

omit [Countable Γ] [TopologicalSpace.SeparableSpace B] in
@[simp] theorem sourcePullback_mk (β : CStarAlgebraAction Γ B)
    (c : BundledGradedKasparovCycle.{0,max uΓ uB,uC,uF}
      (sourceAction β) η (sourceGrading β) δC) :
    sourcePullback β (GradedKasparovHomotopyClass.mk c) =
      GradedKasparovHomotopyClass.mk
        (c.sourcePullback (targetAction β) (targetGrading β)
          (targetAction_preservesGrading β) (equiv β).symm.starAlgEquiv.toNonUnitalStarAlgHom
          (equiv β).symm.action_intertwine (equiv β).symm.grading_intertwine) := rfl

omit [Countable Γ] [TopologicalSpace.SeparableSpace B] in
/-- Pulling a coordinate-pair source forward to the crossed Clifford algebra
and then back by the canonical inverse source map restores the actual full
homotopy class. The witness is the identity on the original module; its
representation identity is the actual inverse equation of the pair star
equivalence. -/
theorem sourcePullback_forward_cancel (β : CStarAlgebraAction Γ B)
    (y : GradedKasparovHomotopyClass.{0,max uΓ uB,uC,uF}
      (targetAction β) η (targetGrading β) δC) :
    sourcePullback β
        (GradedKasparovHomotopyClass.sourcePullback
          (sourceAction β) (sourceGrading β) (sourceAction_preservesGrading β)
          (equiv β).starAlgEquiv.toNonUnitalStarAlgHom
          (equiv β).action_intertwine (equiv β).grading_intertwine y) = y := by
  refine Quotient.inductionOn y ?_
  intro c
  change GradedKasparovHomotopyClass.mk
      ((c.sourcePullback (sourceAction β) (sourceGrading β)
        (sourceAction_preservesGrading β) (equiv β).starAlgEquiv.toNonUnitalStarAlgHom
        (equiv β).action_intertwine (equiv β).grading_intertwine).sourcePullback
          (targetAction β) (targetGrading β) (targetAction_preservesGrading β)
          (equiv β).symm.starAlgEquiv.toNonUnitalStarAlgHom
          (equiv β).symm.action_intertwine (equiv β).symm.grading_intertwine) =
    GradedKasparovHomotopyClass.mk c
  apply GradedKasparovHomotopyClass.mk_eq_of_iso
  refine
    { moduleEquiv := HilbertModuleEquiv.refl
      grading_intertwine := fun _ => rfl
      action_intertwine := fun _ _ => rfl
      representation_intertwine := ?_
      operator_intertwine := fun _ => rfl }
  intro a x
  change c.cycle.representation
      ((equiv β).starAlgEquiv ((equiv β).starAlgEquiv.symm a)) x =
    c.cycle.representation a x
  rw [(equiv β).starAlgEquiv.apply_symm_apply]

/-- Simultaneously changing the intermediate coefficient of the first class
and the source of the second class preserves the genuine product. This is the
exact transport theorem needed when an odd intermediate coefficient is
identified with the actual Clifford pair after descent. -/
theorem changeIntermediate_product [TopologicalSpace.SeparableSpace A]
    (β : CStarAlgebraAction Γ B)
    (x : GradedKasparovHomotopyClass.{0,uA,max uΓ uB,uE}
      α (sourceAction β) δA (sourceGrading β))
    (y : GradedKasparovHomotopyClass.{0,max uΓ uB,uC,uF}
      (sourceAction β) η (sourceGrading β) δC) :
    GroupUniverseProduct.product x y =
      GroupUniverseProduct.product (changeCoefficients β x) (sourcePullback β y) := by
  have h := GroupUniverseProductCoefficientEquivalence.changeCoefficients_product
    (equiv β) (GroupUniverseProductCoefficientEquivalence.identityEquiv η δC)
    (sourceAction_preservesGrading β) x y
  simpa only [GroupUniverseProductCoefficientEquivalence.secondCoefficientInput,
    GroupUniverseProductCoefficientEquivalence.changeCoefficients_identity,
    changeCoefficients, sourcePullback] using h

end Classes

section FinalCoefficientProduct
variable [Countable Γ] [TopologicalSpace.SeparableSpace B]
  {A : Type uA} {C : Type uC}
  [NonUnitalCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace C]
  {α : CStarAlgebraAction Unit A} {η : CStarAlgebraAction Unit C}
  {δA : CStarGrading A} {δC : CStarGrading C}

/-- Changing the final crossed Clifford coefficient commutes with the genuine
product, by the existing full coefficient-change product theorem. -/
theorem changeCoefficients_product (β : CStarAlgebraAction Γ B)
    (hη : η.PreservesGrading δC)
    (x : GradedKasparovHomotopyClass.{0,uA,uC,uE} α η δA δC)
    (y : GradedKasparovHomotopyClass.{0,uC,max uΓ uB,uF}
      η (sourceAction β) δC (sourceGrading β)) :
    changeCoefficients β (GroupUniverseProduct.product x y) =
      GroupUniverseProduct.product x (changeCoefficients β y) :=
  GroupUniverseProductCoefficientEquivalence.changeFinalCoefficients_product
    (equiv β) hη x y

end FinalCoefficientProduct

section SourceProduct
variable [Countable Γ] [TopologicalSpace.SeparableSpace B]
  {C : Type uC} {D : Type uD}
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace C]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [TopologicalSpace.SeparableSpace D]
  {η : CStarAlgebraAction Unit C} {ζ : CStarAlgebraAction Unit D}
  {δC : CStarGrading C} {δD : CStarGrading D}

/-- Pulling the first source back along the inverse crossed-pair equivalence
commutes with the genuine product. -/
theorem sourcePullback_product (β : CStarAlgebraAction Γ B)
    (x : GradedKasparovHomotopyClass.{0,max uΓ uB,uC,uE}
      (sourceAction β) η (sourceGrading β) δC)
    (y : GradedKasparovHomotopyClass.{0,uC,uD,uF} η ζ δC δD) :
    sourcePullback β (GroupUniverseProduct.product x y) =
      GroupUniverseProduct.product (sourcePullback β x) y :=
  GroupUniverseProduct.sourcePullback_product
    (targetAction β) (targetGrading β) (targetAction_preservesGrading β)
    (equiv β).symm.starAlgEquiv.toNonUnitalStarAlgHom
    (equiv β).symm.action_intertwine (equiv β).symm.grading_intertwine x y

end SourceProduct
end BC4lean.KKTheory.KasparovDescentPairCoefficientEquiv
