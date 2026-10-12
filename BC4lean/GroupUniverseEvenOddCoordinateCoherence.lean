import BC4lean.GroupUniverseOddFirstParityProduct
import BC4lean.GroupUniverseParityProduct
import BC4lean.GroupUniverseProductCoefficientEquivalence

/-! # Genuine coherence of the independent-universe even-odd routes

The tensor Clifford and coordinate bridges use the actual complete
coefficient equivalence. Its proved product criterion transport identifies
the original even-odd product with the coordinate product. Thus mixed
associativity applies to the existing product rather than a replacement.
-/

noncomputable section
universe uΓ uA uB uC uD uE uF uG
namespace BC4lean.KKTheory.GroupUniverseOddFirstParityProduct
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C] [Countable Γ]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
open GroupUniverseProductCoefficientEquivalence

omit [TopologicalSpace.SeparableSpace A] [Countable Γ] in
theorem coordinateClass_tensorOddClass
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α (cliffordTensorAction β)
      CStarGrading.trivial cliffordTensorGrading) :
    GroupUniverseCliffordCoordinateBridge.gradedOddClass (GroupUniverseCliffordBridge.oddClass x) =
      changeCoefficients (cliffordTensorGradedCoefficientEquiv β) x := by
  have h : GroupUniverseCliffordBridge.oddClass x =
      GroupUniverseCliffordCoordinateBridge.oddClass
        (changeCoefficients (cliffordTensorGradedCoefficientEquiv β) x) := by
    refine Quotient.inductionOn x ?_
    intro c
    rfl
  rw [h, GroupUniverseCliffordCoordinateBridge.gradedOddClass_oddClass]

omit [TopologicalSpace.SeparableSpace A] [Countable Γ] in
theorem coordinateClass_gradedOddClass (x : OddKK.{uΓ,uA,uB,uE} α β) :
    changeCoefficients (cliffordTensorGradedCoefficientEquiv β)
      (GroupUniverseCliffordBridge.gradedOddClass x) =
    GroupUniverseCliffordCoordinateBridge.gradedOddClass x := by
  rw [← coordinateClass_tensorOddClass, GroupUniverseCliffordBridge.oddClass_gradedOddClass]

theorem coordinateClass_evenOddProduct (x : KasparovHomotopyClass.{uΓ,uA,uB,uE} α β)
    (y : OddKK.{uΓ,uB,uC,uF} β γ) :
    GroupUniverseCliffordCoordinateBridge.gradedOddClass (GroupUniverseParityProduct.evenOddProduct x y) =
      GroupUniverseProduct.product (GroupUniverseEvenBridge.gradedClass x)
        (GroupUniverseCliffordCoordinateBridge.gradedOddClass y) := by
  rw [GroupUniverseParityProduct.evenOddProduct, coordinateClass_tensorOddClass,
    changeFinalCoefficients_product (cliffordTensorGradedCoefficientEquiv γ)
      β.preservesGrading_trivial, coordinateClass_gradedOddClass]

theorem coordinateEvenOddProduct_eq_evenOddProduct
    (x : KasparovHomotopyClass.{uΓ,uA,uB,uE} α β) (y : OddKK.{uΓ,uB,uC,uF} β γ) :
    coordinateEvenOddProduct x y = GroupUniverseParityProduct.evenOddProduct x y := by
  apply GroupUniverseCliffordCoordinateBridge.gradedOddClass_injective
  rw [gradedOddClass_coordinateEvenOddProduct, coordinateClass_evenOddProduct]

end BC4lean.KKTheory.GroupUniverseOddFirstParityProduct
