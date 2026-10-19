import BC4lean.KasparovDescentNativeClassMaps
import BC4lean.KasparovDescentEvenGradedCoherence
import BC4lean.KasparovDescentCliffordExpansionIso
import BC4lean.KasparovDescentCliffordSignedSourceIso
import BC4lean.KasparovDescentCliffordExternalEvenIso
import BC4lean.KasparovDescentClass
import BC4lean.GroupUniverseCliffordCoordinateBridge
import BC4lean.GroupUniverseOddSourceClass
import BC4lean.GroupUniverseExternalEvenClass

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Native bridge coherence from actual descended whole-cycle unitaries

Every class equality below is obtained by
quotient induction from a saved actual whole-cycle isomorphism. The only
source inverse cancellation uses the actual pair algebra equivalence.
No assumed native compatibility field is used. In particular no unproved
injectivity of the signed-source class map is invoked.
-/

noncomputable section
namespace BC4lean.KKTheory.GroupUniverseProductCoefficientEquivalence
variable {Γ A B B' : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra B'] [PartialOrder B'] [StarOrderedRing B']
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace B']
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {β' : CStarAlgebraAction Γ B'}
  {δA δA' : CStarGrading A} {δB : CStarGrading B} {δB' : CStarGrading B'}

/-- Only equality transport of a source grading is moved past an existing
actual coefficient change; equality induction proves the law. -/
theorem regrade_changeCoefficients_source (hA : δA = δA')
    (e : GradedCoefficientEquiv β δB β' δB')
    (x : GradedKasparovHomotopyClass α β δA δB) :
    GradedKasparovHomotopyClass.regrade hA rfl (changeCoefficients e x) =
      changeCoefficients e (GradedKasparovHomotopyClass.regrade hA rfl x) := by
  subst δA'; rfl
end BC4lean.KKTheory.GroupUniverseProductCoefficientEquivalence

namespace BC4lean.KKTheory.KasparovDescentPairCoefficientEquiv
variable {Γ B C : Type*} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C]
  {η : CStarAlgebraAction Unit C} {δC δC' : CStarGrading C}

omit [Countable Γ] [TopologicalSpace.SeparableSpace B] in
/-- Coefficient-grading equality transport commutes with the actual inverse
pair source pullback, by equality induction. -/
theorem regrade_sourcePullback_coefficient (β : CStarAlgebraAction Γ B) (hC : δC = δC')
    (y : GradedKasparovHomotopyClass (sourceAction β) η (sourceGrading β) δC) :
    GradedKasparovHomotopyClass.regrade rfl hC (sourcePullback β y) =
      sourcePullback β (GradedKasparovHomotopyClass.regrade rfl hC y) := by
  subst δC'; rfl
end BC4lean.KKTheory.KasparovDescentPairCoefficientEquiv

universe uΓ uA uB uE
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)

omit [TopologicalSpace.SeparableSpace A] in
/-- The genuine even/graded bridge commutes with actual descent. -/
theorem evenGradedClass_gradedClass
    (x : KasparovHomotopyClass.{uΓ,uA,uB,uE} α β) :
    evenGradedClass α β (GroupUniverseEvenBridge.gradedClass x) =
      GroupUniverseEvenBridge.gradedClass (evenClass β α x) := by
  refine Quotient.inductionOn' x ?_
  intro c
  change evenGradedClass α β
      (GroupUniverseEvenBridge.gradedClass (KasparovHomotopyClass.mk c)) =
    GroupUniverseEvenBridge.gradedClass (evenClass β α (KasparovHomotopyClass.mk c))
  unfold evenGradedClass
  rw [GroupUniverseEvenBridge.gradedClass_mk, gradedClass_mk,
    GradedKasparovHomotopyClass.regrade_mk, evenClass_mk,
    GroupUniverseEvenBridge.gradedClass_mk]
  exact GradedKasparovHomotopyClass.mk_eq_of_iso (evenGradedDescentIso β α c.cycle)

omit [TopologicalSpace.SeparableSpace A] in
/-- Actual coordinate expansion coherence reaches the native odd quotient. -/
theorem coordinateGradedClass_gradedOddClass (x : OddKK.{uΓ,uA,uB,uE} α β) :
    coordinateGradedClass α β (GroupUniverseCliffordCoordinateBridge.gradedOddClass x) =
      GroupUniverseCliffordCoordinateBridge.gradedOddClass (oddClass β α x) := by
  refine Quotient.inductionOn' x ?_
  intro c
  change coordinateGradedClass α β
      (GroupUniverseCliffordCoordinateBridge.gradedOddClass (OddKK.mk c)) =
    GroupUniverseCliffordCoordinateBridge.gradedOddClass (oddClass β α (OddKK.mk c))
  unfold coordinateGradedClass
  rw [GroupUniverseCliffordCoordinateBridge.gradedOddClass_mk, gradedClass_mk]
  change GradedKasparovHomotopyClass.regrade (reducedCrossedProductGrading_trivial α) rfl
      (GroupUniverseProductCoefficientEquivalence.changeCoefficients
        (KasparovDescentPairCoefficientEquiv.equiv β)
        (GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
          (gradedCycle (cliffordCoefficientAction β) α c.cycle.cliffordExpansion)))) = _
  rw [GroupUniverseProductCoefficientEquivalence.regrade_changeCoefficients_source,
    GradedKasparovHomotopyClass.regrade_mk,
    GroupUniverseProductCoefficientEquivalence.changeCoefficients_mk]
  have hiso := GradedKasparovHomotopyClass.mk_eq_of_iso
    (c := BundledGradedKasparovCycle.of
      (descendedCliffordExpansion (E := c.carrier) β α c.cycle))
    (d := BundledGradedKasparovCycle.of
      (oddCycle (E := c.carrier) β α c.cycle).cliffordExpansion)
    (cliffordExpansionDescentIso (E := c.carrier) β α c.cycle)
  have hodd := congrArg
    (fun y : OddKK.{0,max uΓ uA,max uΓ uB,max uE (max uΓ uB)}
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β)) =>
      GroupUniverseCliffordCoordinateBridge.gradedOddClass y)
    (oddClass_mk β α c)
  have hbridge := GroupUniverseCliffordCoordinateBridge.gradedOddClass_mk (bundledOddCycle β α c)
  exact hiso.trans (hodd.trans hbridge).symm

omit [TopologicalSpace.SeparableSpace A] in
/-- Actual signed-source expansion coherence, using the constructed inverse
pair source map and its proved forward/inverse cancellation. -/
theorem signedGradedClass_sourceClass (x : OddKK.{uΓ,uA,uB,uE} α β) :
    signedGradedClass α β (GroupUniverseOddSourceClass.sourceClass x) =
      GroupUniverseOddSourceClass.sourceClass (oddClass β α x) := by
  refine Quotient.inductionOn' x ?_
  intro c
  change signedGradedClass α β (GroupUniverseOddSourceClass.sourceClass (OddKK.mk c)) =
    GroupUniverseOddSourceClass.sourceClass (oddClass β α (OddKK.mk c))
  unfold signedGradedClass
  rw [GroupUniverseOddSourceClass.sourceClass_mk, gradedClass_mk,
    KasparovDescentPairCoefficientEquiv.regrade_sourcePullback_coefficient,
    GradedKasparovHomotopyClass.regrade_mk, oddClass_mk,
    GroupUniverseOddSourceClass.sourceClass_mk]
  have h := GradedKasparovHomotopyClass.mk_eq_of_iso
    (c := BundledGradedKasparovCycle.of (descendedSignedSource β α c.cycle))
    (d := BundledGradedKasparovCycle.of (signedSourceOfDescent β α c.cycle))
    (signedSourceDescentIso β α c.cycle)
  have h' := congrArg (KasparovDescentPairCoefficientEquiv.sourcePullback α) h
  exact h'.trans (KasparovDescentPairCoefficientEquiv.sourcePullback_forward_cancel α
    (GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
      (CliffordOddSourceCycle.cycle (oddCycle β α c.cycle)))))

omit [TopologicalSpace.SeparableSpace A] in
/-- Actual external even coherence supplies the odd-even branch through its
original coordinate/external construction. No signed-source injectivity is needed. -/
theorem externalGradedClass_externalClass
    (x : KasparovHomotopyClass.{uΓ,uA,uB,uE} α β) :
    externalGradedClass α β (GroupUniverseExternalEvenClass.externalClass x) =
      GroupUniverseExternalEvenClass.externalClass (evenClass β α x) := by
  refine Quotient.inductionOn' x ?_
  intro c
  change externalGradedClass α β
      (GroupUniverseExternalEvenClass.externalClass (KasparovHomotopyClass.mk c)) =
    GroupUniverseExternalEvenClass.externalClass (evenClass β α (KasparovHomotopyClass.mk c))
  unfold externalGradedClass
  rw [GroupUniverseExternalEvenClass.externalClass_mk, gradedClass_mk,
    KasparovDescentPairCoefficientEquiv.changeCoefficients_mk,
    evenClass_mk, GroupUniverseExternalEvenClass.externalClass_mk]
  have h := GradedKasparovHomotopyClass.mk_eq_of_iso
    (c := BundledGradedKasparovCycle.of (descendedExternalEven β α c.cycle))
    (d := BundledGradedKasparovCycle.of (externalEvenOfDescent β α c.cycle))
    (externalEvenDescentIso β α c.cycle)
  have h' := congrArg (KasparovDescentPairCoefficientEquiv.sourcePullback α) h
  exact h'.trans (KasparovDescentPairCoefficientEquiv.sourcePullback_forward_cancel α
    (GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
      (CliffordExternalEvenCycle.cycle
        (GradedKasparovCycle.ofKasparovCycle (evenCycle β α c.cycle))))))

end BC4lean.KKTheory.KasparovDescent
