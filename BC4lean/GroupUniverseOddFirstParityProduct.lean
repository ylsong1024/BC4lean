import BC4lean.GroupUniverseProduct
import BC4lean.GroupUniverseCliffordCoordinateBridge
import BC4lean.GroupUniverseExternalEvenClass
import BC4lean.GroupUniverseExternalOddClass
import BC4lean.GroupUniverseMatrixMoritaBridge

/-! # Actual odd-first parity products with independent universes

Odd-even uses the genuine Koszul external even cycle and returns the odd
full quotient. Odd-odd uses the actual Pauli source and row extension,
then the genuine graded product and column Morita map. Its actual carrier
universe is max(uE,uF,uC). All classes and addition laws come from actual
arbitrary full witnesses, whole tensor unitaries, and product uniqueness.
The coordinate even-odd route is retained for genuine mixed associativity.
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
open GroupUniverseCliffordCoordinateBridge

def oddEvenProduct (x : OddKK.{uΓ,uA,uB,uE} α β)
    (y : KasparovHomotopyClass.{uΓ,uB,uC,uF} β γ) :
    OddKK.{uΓ,uA,uC,max uE uF} α γ :=
  oddClass (GroupUniverseProduct.product (gradedOddClass x)
    (GroupUniverseExternalEvenClass.externalClass y))

@[simp] theorem gradedOddClass_oddEvenProduct
    (x : OddKK.{uΓ,uA,uB,uE} α β) (y : KasparovHomotopyClass.{uΓ,uB,uC,uF} β γ) :
    gradedOddClass (oddEvenProduct x y) = GroupUniverseProduct.product (gradedOddClass x)
      (GroupUniverseExternalEvenClass.externalClass y) := gradedOddClass_oddClass _

theorem oddEvenProduct_add_first (x x' : OddKK.{uΓ,uA,uB,uE} α β)
    (y : KasparovHomotopyClass.{uΓ,uB,uC,uF} β γ) :
    oddEvenProduct (x + x') y = oddEvenProduct x y + oddEvenProduct x' y := by
  unfold oddEvenProduct
  rw [gradedOddClass_add, GroupUniverseProduct.add_product, oddClass_add]

theorem oddEvenProduct_add_second (x : OddKK.{uΓ,uA,uB,uE} α β)
    (y y' : KasparovHomotopyClass.{uΓ,uB,uC,uF} β γ) :
    oddEvenProduct x (y + y') = oddEvenProduct x y + oddEvenProduct x y' := by
  unfold oddEvenProduct
  rw [GroupUniverseExternalEvenClass.externalClass_add, GroupUniverseProduct.product_add, oddClass_add]

def oddOddProduct (x : OddKK.{uΓ,uA,uB,uE} α β) (y : OddKK.{uΓ,uB,uC,uF} β γ) :
    KasparovHomotopyClass.{uΓ,uA,uC,max (max uE uF) uC} α γ :=
  GroupUniverseMatrixMoritaBridge.evenClass (GroupUniverseProduct.product (gradedOddClass x)
    (GroupUniverseExternalOddClass.coordinateClass y))

theorem oddOddProduct_add_first (x x' : OddKK.{uΓ,uA,uB,uE} α β)
    (y : OddKK.{uΓ,uB,uC,uF} β γ) :
    oddOddProduct (x + x') y = oddOddProduct x y + oddOddProduct x' y := by
  unfold oddOddProduct
  rw [gradedOddClass_add, GroupUniverseProduct.add_product, GroupUniverseMatrixMoritaBridge.evenClass_add]

theorem oddOddProduct_add_second (x : OddKK.{uΓ,uA,uB,uE} α β)
    (y y' : OddKK.{uΓ,uB,uC,uF} β γ) :
    oddOddProduct x (y + y') = oddOddProduct x y + oddOddProduct x y' := by
  unfold oddOddProduct
  rw [GroupUniverseExternalOddClass.coordinateClass_add, GroupUniverseProduct.product_add,
    GroupUniverseMatrixMoritaBridge.evenClass_add]

def coordinateEvenOddProduct (x : KasparovHomotopyClass.{uΓ,uA,uB,uE} α β)
    (y : OddKK.{uΓ,uB,uC,uF} β γ) : OddKK.{uΓ,uA,uC,max uE uF} α γ :=
  oddClass (GroupUniverseProduct.product (GroupUniverseEvenBridge.gradedClass x) (gradedOddClass y))

@[simp] theorem gradedOddClass_coordinateEvenOddProduct
    (x : KasparovHomotopyClass.{uΓ,uA,uB,uE} α β) (y : OddKK.{uΓ,uB,uC,uF} β γ) :
    gradedOddClass (coordinateEvenOddProduct x y) =
      GroupUniverseProduct.product (GroupUniverseEvenBridge.gradedClass x) (gradedOddClass y) :=
  gradedOddClass_oddClass _

theorem coordinateEvenOddProduct_add_first
    (x x' : KasparovHomotopyClass.{uΓ,uA,uB,uE} α β) (y : OddKK.{uΓ,uB,uC,uF} β γ) :
    coordinateEvenOddProduct (x + x') y =
      coordinateEvenOddProduct x y + coordinateEvenOddProduct x' y := by
  unfold coordinateEvenOddProduct
  rw [GroupUniverseEvenBridge.gradedClass_add, GroupUniverseProduct.add_product, oddClass_add]

theorem coordinateEvenOddProduct_add_second
    (x : KasparovHomotopyClass.{uΓ,uA,uB,uE} α β) (y y' : OddKK.{uΓ,uB,uC,uF} β γ) :
    coordinateEvenOddProduct x (y + y') =
      coordinateEvenOddProduct x y + coordinateEvenOddProduct x y' := by
  unfold coordinateEvenOddProduct
  rw [gradedOddClass_add, GroupUniverseProduct.product_add, oddClass_add]

end BC4lean.KKTheory.GroupUniverseOddFirstParityProduct
