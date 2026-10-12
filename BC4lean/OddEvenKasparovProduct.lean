import BC4lean.CliffordCoordinateKasparovClassEquiv
import BC4lean.CliffordExternalEvenQuotient
import BC4lean.GradedKasparovProductSecondAdditivity

/-! # Genuine odd-by-even products on the chapter's established groups

The even second input has its actual Koszul external Clifford cycle and
its same arbitrary-module full interval witness. The first input uses the
actual odd parity equivalence. The genuine full graded product is then
extracted by the actual plus coefficient range. Both addition laws follow
from the whole external sum unitary and the actual graded product laws.
-/

noncomputable section
universe u
namespace BC4lean.KKTheory.OddKK

variable {Γ A B C : Type u} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C] [Countable Γ]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

open CliffordCoordinateKasparovClassEquiv

def productEven (x : OddKK.{u,u,u,u} α β) (y : KasparovHomotopyClass.{u,u,u,u} β γ) :
    OddKK.{u,u,u,u} α γ :=
  oddClass (GradedKasparovHomotopyClass.product (coordinateClass x) (cliffordExternalEvenClass y))

@[simp] theorem coordinateClass_productEven
    (x : OddKK.{u,u,u,u} α β) (y : KasparovHomotopyClass.{u,u,u,u} β γ) :
    coordinateClass (productEven x y) =
      GradedKasparovHomotopyClass.product (coordinateClass x) (cliffordExternalEvenClass y) :=
  coordinateClass_oddClass _

/-- The genuine raw representative uses the actual chosen product
operator and the actual coefficient-range odd extraction. -/
theorem productEven_mk (c : BundledOddKasparovCycle.{u,u,u,u} α β)
    (d : BundledKasparovCycle.{u,u,u,u} β γ) :
    productEven (mk c) (KasparovHomotopyClass.mk d) =
      mk ((c.cliffordExpansion.product (BundledGradedKasparovCycle.of
        (CliffordExternalEvenCycle.cycle (GradedKasparovCycle.ofKasparovCycle d.cycle)))).cliffordExtraction) := rfl

theorem add_productEven (x x' : OddKK.{u,u,u,u} α β)
    (y : KasparovHomotopyClass.{u,u,u,u} β γ) :
    productEven (x + x') y = productEven x y + productEven x' y := by
  apply coordinateClass_injective
  simp only [coordinateClass_productEven, coordinateClass_add]
  exact GradedKasparovHomotopyClass.add_product (coordinateClass x) (coordinateClass x')
    (cliffordExternalEvenClass y)

theorem productEven_add (x : OddKK.{u,u,u,u} α β)
    (y y' : KasparovHomotopyClass.{u,u,u,u} β γ) :
    productEven x (y + y') = productEven x y + productEven x y' := by
  apply coordinateClass_injective
  simp only [coordinateClass_productEven, coordinateClass_add, cliffordExternalEvenClass_add]
  exact GradedKasparovHomotopyClass.product_add (coordinateClass x)
    (cliffordExternalEvenClass y) (cliffordExternalEvenClass y')

theorem zero_productEven (y : KasparovHomotopyClass.{u,u,u,u} β γ) :
    productEven (0 : OddKK.{u,u,u,u} α β) y = 0 := by
  have h := add_productEven (0 : OddKK.{u,u,u,u} α β) 0 y
  rw [zero_add] at h
  have h' : productEven (0 : OddKK.{u,u,u,u} α β) y + 0 =
      productEven (0 : OddKK.{u,u,u,u} α β) y + productEven 0 y := by
    simpa only [add_zero] using h
  exact (add_left_cancel h').symm

theorem productEven_zero (x : OddKK.{u,u,u,u} α β) :
    productEven x (0 : KasparovHomotopyClass.{u,u,u,u} β γ) = 0 := by
  have h := productEven_add x (0 : KasparovHomotopyClass.{u,u,u,u} β γ) 0
  rw [zero_add] at h
  have h' : productEven x (0 : KasparovHomotopyClass.{u,u,u,u} β γ) + 0 =
      productEven x (0 : KasparovHomotopyClass.{u,u,u,u} β γ) + productEven x 0 := by
    simpa only [add_zero] using h
  exact (add_left_cancel h').symm

def productEvenAddHom : OddKK.{u,u,u,u} α β →+
    (KasparovHomotopyClass.{u,u,u,u} β γ →+ OddKK.{u,u,u,u} α γ) where
  toFun x := {
    toFun := productEven x
    map_zero' := productEven_zero x
    map_add' := productEven_add x }
  map_zero' := by ext y; exact zero_productEven y
  map_add' x x' := by ext y; exact add_productEven x x' y

end BC4lean.KKTheory.OddKK
