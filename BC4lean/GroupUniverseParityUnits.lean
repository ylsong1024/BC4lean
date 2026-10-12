import BC4lean.GroupUniverseParityHomCycle
import BC4lean.CliffordExternalEvenCycleIso

/-! # Actual ambient units for all parity products

The even unit is the genuine zero-operator standard identity cycle,
placed in the chosen module universe by its whole lift unitary. The
external even extension commutes with this lift by actual entire-cycle
isomorphisms. True graded units then prove both even and odd unit laws.
-/

noncomputable section
universe uΓ uA uB uC uE v
namespace BC4lean.KKTheory.GroupUniverseParityUnits
open GroupUniverseParityGroup

section Mixed
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

def leftEvenProduct (p : Bool) (h : KasparovHomotopyClass.{uΓ,uA,uB,uE} α β) :
    KKParityGroup.{uΓ,uB,uC,uE} p β γ → KKParityGroup.{uΓ,uA,uC,uE} p α γ := by
  cases p
  · exact GroupUniverseParityProduct.evenProduct h
  · exact GroupUniverseParityProduct.evenOddProduct h

def rightEvenProduct (p : Bool) (x : KKParityGroup.{uΓ,uA,uB,uE} p α β) :
    KasparovHomotopyClass.{uΓ,uB,uC,uE} β γ → KKParityGroup.{uΓ,uA,uC,uE} p α γ := by
  cases p
  · exact GroupUniverseParityProduct.evenProduct x
  · exact GroupUniverseOddFirstParityProduct.oddEvenProduct x

end Mixed

section Identity
variable {Γ : Type uΓ} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]

def identity (β : CStarAlgebraAction Γ B) :
    KasparovHomotopyClass.{uΓ,uB,uB,max uB v} β β :=
  GroupUniverseEvenBridge.evenClass (GradedKasparovHomotopyClass.ulift.{uΓ,uB,uB,uB,v}
    (GroupUniverseProduct.identity β CStarGrading.trivial β.preservesGrading_trivial))

theorem homClass_id (β : CStarAlgebraAction Γ B) :
    GroupUniverseParityHomCycle.homClass.{uΓ,uB,uB,v}
      (NonUnitalStarAlgHom.id ℂ B) (fun _ _ => rfl) = identity.{uΓ,uB,v} β := by
  unfold GroupUniverseParityHomCycle.homClass identity
  rw [GroupUniverseCoefficientPushforward.homClass_identity]

end Identity

section ExternalLift
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

theorem externalClass_evenClass_ulift
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β
      CStarGrading.trivial CStarGrading.trivial) :
    GroupUniverseExternalEvenClass.externalClass (GroupUniverseEvenBridge.evenClass
      (GradedKasparovHomotopyClass.ulift.{uΓ,uA,uB,uE,v} x)) =
    GradedKasparovHomotopyClass.ulift.{uΓ,uA,uB,uE,v}
      (GroupUniverseExternalEvenClass.externalClass (GroupUniverseEvenBridge.evenClass x)) := by
  refine Quotient.inductionOn x ?_
  intro c
  simp only [GradedKasparovHomotopyClass.ulift_mk, GroupUniverseEvenBridge.evenClass_mk,
    GroupUniverseExternalEvenClass.externalClass_mk, GroupUniverseEvenBase.toEven,
    GradedKasparovCycle.ofKasparovCycle_toKasparovCycle]
  exact GradedKasparovHomotopyClass.mk_eq_of_iso
    ((CliffordExternalEvenCycle.iso c.cycle.uliftIso).symm.trans
      ((CliffordExternalEvenCycle.cycle c.cycle).uliftIso))

theorem externalClass_identity :
    GroupUniverseExternalEvenClass.externalClass (identity.{uΓ,uB,v} β) =
    GradedKasparovHomotopyClass.ulift.{uΓ,uB,uB,uB,v}
      (GroupUniverseProduct.identity (cliffordCoefficientAction β) cliffordCoefficientGrading
        (cliffordCoefficientAction_preservesGrading β)) := by
  unfold identity
  rw [externalClass_evenClass_ulift]
  exact congrArg (GradedKasparovHomotopyClass.ulift.{uΓ,uB,uB,uB,v})
    GroupUniverseOddFirstParityProduct.externalEvenClass_identity

end ExternalLift

section Units
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-- The genuine ambient standard unit acts on both even and odd classes. -/
theorem right_identity (p : Bool)
    (x : KKParityGroup.{uΓ,uA,uB,max uE (max uA uB)} p α β) :
    rightEvenProduct p x (identity.{uΓ,uB,max uE (max uA uB)} β) = x := by
  cases p
  · apply GroupUniverseEvenBridge.gradedClass_injective
    rw [rightEvenProduct, GroupUniverseParityProduct.gradedClass_evenProduct,
      identity, GroupUniverseEvenBridge.gradedClass_evenClass,
      ← GroupUniverseProduct.product_ulift_second, GroupUniverseProduct.product_right_identity]
    exact GradedKasparovHomotopyClass.ulift_eq_self.{uΓ,uA,uB,0,max uE (max uA uB)} _
  · apply GroupUniverseCliffordCoordinateBridge.gradedOddClass_injective
    rw [rightEvenProduct, GroupUniverseOddFirstParityProduct.gradedOddClass_oddEvenProduct,
      externalClass_identity, ← GroupUniverseProduct.product_ulift_second,
      GroupUniverseProduct.product_right_identity]
    exact GradedKasparovHomotopyClass.ulift_eq_self.{uΓ,uA,uB,0,max uE (max uA uB)} _

/-- The same genuine ambient standard unit acts from the first algebra. -/
theorem left_identity (p : Bool)
    (x : KKParityGroup.{uΓ,uA,uB,max uE (max uA uB)} p α β) :
    leftEvenProduct p (identity.{uΓ,uA,max uE (max uA uB)} α) x = x := by
  cases p
  · apply GroupUniverseEvenBridge.gradedClass_injective
    rw [leftEvenProduct, GroupUniverseParityProduct.gradedClass_evenProduct,
      identity, GroupUniverseEvenBridge.gradedClass_evenClass,
      ← GroupUniverseProduct.product_ulift_first, GroupUniverseProduct.product_left_identity]
    exact GradedKasparovHomotopyClass.ulift_eq_self.{uΓ,uA,uB,0,max uE (max uA uB)} _
  · apply GroupUniverseCliffordCoordinateBridge.gradedOddClass_injective
    rw [leftEvenProduct, GroupUniverseOddFirstParityProduct.coordinateClass_evenOddProduct,
      identity, GroupUniverseEvenBridge.gradedClass_evenClass,
      ← GroupUniverseProduct.product_ulift_first, GroupUniverseProduct.product_left_identity]
    exact GradedKasparovHomotopyClass.ulift_eq_self.{uΓ,uA,uB,0,max uE (max uA uB)} _

end Units
end BC4lean.KKTheory.GroupUniverseParityUnits
