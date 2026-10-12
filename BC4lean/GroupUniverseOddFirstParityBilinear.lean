import BC4lean.GroupUniverseOddFirstParityProduct
import BC4lean.GroupUniverseParityProduct
import BC4lean.CliffordExternalEvenIdentity

/-! # Genuine bilinear odd-first products and the actual even unit

The proved two addition laws give genuine additive homomorphisms in each
variable on the existing parity groups. The explicit whole standard pair
unitary computes the Koszul external even identity, and the real graded
right-unit witness gives odd-even right identity in the common universe.
-/

noncomputable section
universe uΓ uA uB uC uE uF
namespace BC4lean.KKTheory.GroupUniverseOddFirstParityProduct
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C] [Countable Γ]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

theorem oddEvenProduct_zero_first (y : KasparovHomotopyClass.{uΓ,uB,uC,uF} β γ) :
    oddEvenProduct (0 : OddKK.{uΓ,uA,uB,uE} α β) y = 0 := by
  have h := oddEvenProduct_add_first (0 : OddKK.{uΓ,uA,uB,uE} α β) 0 y
  rw [zero_add] at h
  have h' : oddEvenProduct (0 : OddKK.{uΓ,uA,uB,uE} α β) y + 0 =
      oddEvenProduct (0 : OddKK.{uΓ,uA,uB,uE} α β) y + oddEvenProduct 0 y := by
    simpa only [add_zero] using h
  exact (add_left_cancel h').symm

theorem oddEvenProduct_zero_second (x : OddKK.{uΓ,uA,uB,uE} α β) :
    oddEvenProduct x (0 : KasparovHomotopyClass.{uΓ,uB,uC,uF} β γ) = 0 := by
  have h := oddEvenProduct_add_second x (0 : KasparovHomotopyClass.{uΓ,uB,uC,uF} β γ) 0
  rw [zero_add] at h
  have h' : oddEvenProduct x (0 : KasparovHomotopyClass.{uΓ,uB,uC,uF} β γ) + 0 =
      oddEvenProduct x (0 : KasparovHomotopyClass.{uΓ,uB,uC,uF} β γ) + oddEvenProduct x 0 := by
    simpa only [add_zero] using h
  exact (add_left_cancel h').symm

theorem oddOddProduct_zero_first (y : OddKK.{uΓ,uB,uC,uF} β γ) :
    oddOddProduct (0 : OddKK.{uΓ,uA,uB,uE} α β) y = 0 := by
  have h := oddOddProduct_add_first (0 : OddKK.{uΓ,uA,uB,uE} α β) 0 y
  rw [zero_add] at h
  have h' : oddOddProduct (0 : OddKK.{uΓ,uA,uB,uE} α β) y + 0 =
      oddOddProduct (0 : OddKK.{uΓ,uA,uB,uE} α β) y + oddOddProduct (0 : OddKK.{uΓ,uA,uB,uE} α β) y := by
    simpa only [add_zero] using h
  exact (add_left_cancel h').symm

theorem oddOddProduct_zero_second (x : OddKK.{uΓ,uA,uB,uE} α β) :
    oddOddProduct x (0 : OddKK.{uΓ,uB,uC,uF} β γ) = 0 := by
  have h := oddOddProduct_add_second x (0 : OddKK.{uΓ,uB,uC,uF} β γ) 0
  rw [zero_add] at h
  have h' : oddOddProduct x (0 : OddKK.{uΓ,uB,uC,uF} β γ) + 0 =
      oddOddProduct x (0 : OddKK.{uΓ,uB,uC,uF} β γ) + oddOddProduct x (0 : OddKK.{uΓ,uB,uC,uF} β γ) := by
    simpa only [add_zero] using h
  exact (add_left_cancel h').symm

def oddEvenProductAddHom : OddKK.{uΓ,uA,uB,uE} α β →+
    (KasparovHomotopyClass.{uΓ,uB,uC,uF} β γ →+ OddKK.{uΓ,uA,uC,max uE uF} α γ) where
  toFun x := {
    toFun := oddEvenProduct x
    map_zero' := oddEvenProduct_zero_second x
    map_add' := oddEvenProduct_add_second x }
  map_zero' := by ext y; exact oddEvenProduct_zero_first y
  map_add' x x' := by ext y; exact oddEvenProduct_add_first x x' y

def oddOddProductAddHom : OddKK.{uΓ,uA,uB,uE} α β →+
    (OddKK.{uΓ,uB,uC,uF} β γ →+ KasparovHomotopyClass.{uΓ,uA,uC,max (max uE uF) uC} α γ) where
  toFun x := {
    toFun := oddOddProduct x
    map_zero' := oddOddProduct_zero_second x
    map_add' := oddOddProduct_add_second x }
  map_zero' := by ext y; exact oddOddProduct_zero_first y
  map_add' x x' := by ext y; exact oddOddProduct_add_first x x' y

omit [Countable Γ] in
theorem externalEvenClass_identity :
    GroupUniverseExternalEvenClass.externalClass (GroupUniverseParityProduct.evenIdentity β) =
      GroupUniverseProduct.identity (cliffordCoefficientAction β) cliffordCoefficientGrading
        (cliffordCoefficientAction_preservesGrading β) := by
  change GroupUniverseExternalEvenClass.externalClass (KasparovHomotopyClass.mk (BundledKasparovCycle.of
    ((gradedStandardIdentityCycle β CStarGrading.trivial β.preservesGrading_trivial).toKasparovCycle))) = _
  rw [GroupUniverseExternalEvenClass.externalClass_mk]
  change GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
    (CliffordExternalEvenCycle.cycle (GradedKasparovCycle.ofKasparovCycle
      ((gradedStandardIdentityCycle β CStarGrading.trivial
        β.preservesGrading_trivial).toKasparovCycle)))) = _
  rw [GradedKasparovCycle.ofKasparovCycle_toKasparovCycle]
  exact GradedKasparovHomotopyClass.mk_eq_of_iso (CliffordExternalEvenCycle.standardIdentityIso β).symm

theorem oddEvenProduct_right_identity (x : OddKK.{uΓ,uA,uB,max uE uB} α β) :
    oddEvenProduct x (GroupUniverseParityProduct.evenIdentity β) = x := by
  apply GroupUniverseCliffordCoordinateBridge.gradedOddClass_injective
  rw [gradedOddClass_oddEvenProduct, externalEvenClass_identity]
  exact GroupUniverseProduct.product_right_identity (cliffordCoefficientAction_preservesGrading β) _

end BC4lean.KKTheory.GroupUniverseOddFirstParityProduct
