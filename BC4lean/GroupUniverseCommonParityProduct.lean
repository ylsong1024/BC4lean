import BC4lean.GroupUniverseParityGroup
import BC4lean.GroupUniverseEvenOddSourceProduct
import BC4lean.GroupUniverseOddFirstParityAssociativity
import BC4lean.GroupUniverseOddFirstParityBilinear
import BC4lean.GroupUniverseOddOddSourceProduct
import BC4lean.GroupShrinkEvenBridge
import BC4lean.GroupShrinkOddEquivalence

/-! # The actual four parity products at a common module universe

Group and coefficient universes remain independent. A common Hilbert
module universe contains the coefficient carriers used by the real row
and column tensors. All four branches are the independently constructed
native products. Every original module universe is identified with this
common universe by genuine whole-cycle/full-interval shrinking maps.
-/

noncomputable section
universe uΓ uA uB uC uE v u
namespace BC4lean.KKTheory.GroupUniverseCommonParityProduct
open GroupUniverseParityGroup

section UniverseComparison
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-- The chosen actual module universe does not exclude any full cycle class:
the comparison is its proved whole-module and full-interval equivalence. -/
def universeEquivalence (p : Bool) : KKParityGroup.{uΓ,uA,uB,uE} p α β ≃+
    KKParityGroup.{uΓ,uA,uB,v} p α β := by
  cases p
  · exact GroupShrinkEvenBridge.addEquivalence
  · exact OddKK.shrinkAddEquiv

end UniverseComparison

section Pairs
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

/-- The four branches use the genuine even, Clifford tensor, Koszul external
even, and Pauli-row/column Morita products respectively. -/
def product (p q : Bool) :
    KKParityGroup.{uΓ,uA,uB,max u (max uA (max uB uC))} p α β →
    KKParityGroup.{uΓ,uB,uC,max u (max uA (max uB uC))} q β γ →
    KKParityGroup.{uΓ,uA,uC,max u (max uA (max uB uC))} (Bool.xor p q) α γ := by
  cases p <;> cases q
  · exact GroupUniverseParityProduct.evenProduct
  · exact GroupUniverseParityProduct.evenOddProduct
  · exact GroupUniverseOddFirstParityProduct.oddEvenProduct
  · exact GroupUniverseOddFirstParityProduct.oddOddProduct

theorem product_add_first (p q : Bool)
    (x x' : KKParityGroup.{uΓ,uA,uB,max u (max uA (max uB uC))} p α β)
    (y : KKParityGroup.{uΓ,uB,uC,max u (max uA (max uB uC))} q β γ) :
    product p q (x + x') y = product p q x y + product p q x' y := by
  cases p <;> cases q
  · exact GroupUniverseParityProduct.evenProduct_add_first x x' y
  · exact GroupUniverseParityProduct.evenOddProduct_add_first x x' y
  · exact GroupUniverseOddFirstParityProduct.oddEvenProduct_add_first x x' y
  · exact GroupUniverseOddFirstParityProduct.oddOddProduct_add_first x x' y

theorem product_add_second (p q : Bool)
    (x : KKParityGroup.{uΓ,uA,uB,max u (max uA (max uB uC))} p α β)
    (y y' : KKParityGroup.{uΓ,uB,uC,max u (max uA (max uB uC))} q β γ) :
    product p q x (y + y') = product p q x y + product p q x y' := by
  cases p <;> cases q
  · exact GroupUniverseParityProduct.evenProduct_add_second x y y'
  · exact GroupUniverseParityProduct.evenOddProduct_add_second x y y'
  · exact GroupUniverseOddFirstParityProduct.oddEvenProduct_add_second x y y'
  · exact GroupUniverseOddFirstParityProduct.oddOddProduct_add_second x y y'

/-- Genuine bilinearity of all four actual parity products. -/
def productAddHom (p q : Bool) :
    KKParityGroup.{uΓ,uA,uB,max u (max uA (max uB uC))} p α β →+
    (KKParityGroup.{uΓ,uB,uC,max u (max uA (max uB uC))} q β γ →+
      KKParityGroup.{uΓ,uA,uC,max u (max uA (max uB uC))} (Bool.xor p q) α γ) :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (product p q x) (product_add_second p q x))
    (by intro x x'; ext y; exact product_add_first p q x x' y)

end Pairs

universe uD
section Triples
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
  [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [PartialOrder D] [StarOrderedRing D]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C] [TopologicalSpace.SeparableSpace D]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C} {η : CStarAlgebraAction Γ D}

/-- All eight parity combinations satisfy actual product associativity.
The common module universe contains every intermediate coefficient carrier;
the only dependent cast is the proved associativity of parity addition. -/
theorem product_assoc (p q r : Bool)
    (x : KKParityGroup.{uΓ,uA,uB,max u (max uA (max uB (max uC uD)))} p α β)
    (y : KKParityGroup.{uΓ,uB,uC,max u (max uA (max uB (max uC uD)))} q β γ)
    (z : KKParityGroup.{uΓ,uC,uD,max u (max uA (max uB (max uC uD)))} r γ η) :
    product.{uΓ,uA,uC,uD,max u uB} (Bool.xor p q) r
      (product.{uΓ,uA,uB,uC,max u uD} p q x y) z =
    (by simpa only [Bool.xor_assoc] using
      (product.{uΓ,uA,uB,uD,max u uC} p (Bool.xor q r) x
        (product.{uΓ,uB,uC,uD,max u uA} q r y z)) :
      KKParityGroup.{uΓ,uA,uD,max u (max uA (max uB (max uC uD)))}
        (Bool.xor (Bool.xor p q) r) α η) := by
  cases p <;> cases q <;> cases r
  · exact GroupUniverseParityProduct.evenProduct_assoc x y z
  · exact GroupUniverseParityProduct.evenEvenOddProduct_assoc x y z
  · exact GroupUniverseOddFirstParityProduct.evenOddEvenProduct_assoc x y z
  · exact GroupUniverseOddFirstParityProduct.evenOddOddProduct_assoc x y z
  · exact GroupUniverseOddFirstParityProduct.oddEvenEvenProduct_assoc x y z
  · exact GroupUniverseOddFirstParityProduct.oddEvenOddProduct_assoc x y z
  · exact GroupUniverseOddFirstParityProduct.oddOddEvenProduct_assoc x y z
  · exact GroupUniverseOddFirstParityProduct.oddOddOddProduct_assoc x y z

end Triples
end BC4lean.KKTheory.GroupUniverseCommonParityProduct
