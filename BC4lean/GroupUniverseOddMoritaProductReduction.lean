import BC4lean.GroupUniverseOddSourceEvenProduct
import BC4lean.GroupUniverseEvenOddCoordinateCoherence
import BC4lean.GroupUniverseProductLift

/-! # The actual signed-source computation of the odd-by-odd product

The true row extension is multiplication by its genuine correspondence
cycle. Its actual column inverse cancels by the completed double-tensor
unitary. The original module universe is retained explicitly: the result
is the actual lift of the signed-source product to include `uC`.
-/

noncomputable section
universe uΓ uA uB uC uD uE uF uG
namespace BC4lean.KKTheory.GroupUniverseOddFirstParityProduct
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

/-- The genuine M₂ product has the signed-source value, transported by the
actual whole module lift required by the row/column tensor universe. -/
theorem gradedClass_oddOddProduct_ulift
    (x : OddKK.{uΓ,uA,uB,uE} α β) (y : OddKK.{uΓ,uB,uC,uF} β γ) :
    GroupUniverseEvenBridge.gradedClass (oddOddProduct x y) =
    GradedKasparovHomotopyClass.ulift.{uΓ,uA,uC,max uE uF,uC}
      (GroupUniverseProduct.product (GroupUniverseCliffordCoordinateBridge.gradedOddClass x)
        (GroupUniverseOddSourceClass.sourceClass y)) := by
  unfold oddOddProduct GroupUniverseMatrixMoritaBridge.evenClass
  rw [GroupUniverseEvenBridge.gradedClass_evenClass,
    GroupUniverseMatrixMoritaProduct.toCoefficientClass_product,
    GroupUniverseOddSourceClass.coordinateClass_eq_toMatrixClass,
    GroupUniverseMatrixMoritaBridge.coefficient_roundtrip]
  exact (GroupUniverseProduct.product_ulift_second.{uΓ,uA,uB,uC,uE,uF,uC}
    (GroupUniverseCliffordCoordinateBridge.gradedOddClass x)
    (GroupUniverseOddSourceClass.sourceClass y)).symm

/-- At a common module universe containing the final coefficient universe,
the actual lift is identified with its input by the whole lift unitary. -/
theorem gradedClass_oddOddProduct
    (x : OddKK.{uΓ,uA,uB,max uE uC} α β)
    (y : OddKK.{uΓ,uB,uC,max uF uC} β γ) :
    GroupUniverseEvenBridge.gradedClass (oddOddProduct x y) =
      GroupUniverseProduct.product (GroupUniverseCliffordCoordinateBridge.gradedOddClass x)
        (GroupUniverseOddSourceClass.sourceClass y) := by
  rw [gradedClass_oddOddProduct_ulift]
  exact GradedKasparovHomotopyClass.ulift_eq_self.{uΓ,uA,uC,max uE uF,uC} _

variable {D : Type uD} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [TopologicalSpace.SeparableSpace D] {η : CStarAlgebraAction Γ D}

/-- The existing even-by-odd route satisfies genuine 011 associativity
with independent coefficient and all original module universes. -/
theorem evenOddOddProduct_assoc
    (x : KasparovHomotopyClass.{uΓ,uA,uB,uE} α β)
    (y : OddKK.{uΓ,uB,uC,uF} β γ) (z : OddKK.{uΓ,uC,uD,uG} γ η) :
    oddOddProduct (GroupUniverseParityProduct.evenOddProduct x y) z =
      GroupUniverseParityProduct.evenProduct x (oddOddProduct y z) := by
  apply GroupUniverseEvenBridge.gradedClass_injective
  rw [gradedClass_oddOddProduct_ulift, coordinateClass_evenOddProduct,
    GroupUniverseParityProduct.gradedClass_evenProduct, gradedClass_oddOddProduct_ulift,
    ← GroupUniverseProduct.product_ulift_second]
  exact congrArg
    (GradedKasparovHomotopyClass.ulift.{uΓ,uA,uD,max (max uE uF) uG,uD})
    (GroupUniverseProduct.product_assoc (GroupUniverseEvenBridge.gradedClass x)
      (GroupUniverseCliffordCoordinateBridge.gradedOddClass y)
      (GroupUniverseOddSourceClass.sourceClass z))

/-- Genuine 110 associativity at the common actual module universe which
contains the two distinct intermediate coefficient universes. -/
theorem oddOddEvenProduct_assoc
    (x : OddKK.{uΓ,uA,uB,max uE (max uC uD)} α β)
    (y : OddKK.{uΓ,uB,uC,max uE (max uC uD)} β γ)
    (z : KasparovHomotopyClass.{uΓ,uC,uD,max uE (max uC uD)} γ η) :
    GroupUniverseParityProduct.evenProduct (oddOddProduct x y) z =
      oddOddProduct x (oddEvenProduct y z) := by
  apply GroupUniverseEvenBridge.gradedClass_injective
  rw [GroupUniverseParityProduct.gradedClass_evenProduct, gradedClass_oddOddProduct_ulift,
    gradedClass_oddOddProduct_ulift, GroupUniverseOddSourceClass.sourceClass_oddEvenProduct,
    GradedKasparovHomotopyClass.ulift_eq_self.{uΓ,uA,uC,max uE uD,uC},
    GradedKasparovHomotopyClass.ulift_eq_self.{uΓ,uA,uD,max uE uC,uD}]
  exact GroupUniverseProduct.product_assoc (GroupUniverseCliffordCoordinateBridge.gradedOddClass x)
    (GroupUniverseOddSourceClass.sourceClass y) (GroupUniverseEvenBridge.gradedClass z)

end BC4lean.KKTheory.GroupUniverseOddFirstParityProduct
