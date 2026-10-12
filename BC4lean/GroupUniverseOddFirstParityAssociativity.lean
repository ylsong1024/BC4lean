import BC4lean.GroupUniverseExternalEvenMonoidalClass
import BC4lean.GroupUniverseEvenOddCoordinateCoherence

/-! # Genuine mixed independent-universe associativity in the original route

The proved coordinate coherence identifies the original tensor Clifford
even-odd product. Its mixed associativity is therefore the actual graded
full associativity law through faithful bridges, with no assumed exterior
or Morita product law.
-/

noncomputable section
universe uΓ uA uB uC uD uE uF uG
namespace BC4lean.KKTheory.GroupUniverseOddFirstParityProduct
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C] [TopologicalSpace.SeparableSpace D] [Countable Γ]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C} {η : CStarAlgebraAction Γ D}

theorem evenOddEvenProduct_assoc
    (x : KasparovHomotopyClass.{uΓ,uA,uB,uE} α β) (y : OddKK.{uΓ,uB,uC,uF} β γ)
    (z : KasparovHomotopyClass.{uΓ,uC,uD,uG} γ η) :
    oddEvenProduct (GroupUniverseParityProduct.evenOddProduct x y) z =
      GroupUniverseParityProduct.evenOddProduct x (oddEvenProduct y z) := by
  rw [← coordinateEvenOddProduct_eq_evenOddProduct,
    ← coordinateEvenOddProduct_eq_evenOddProduct]
  exact coordinateEvenOddEvenProduct_assoc x y z

end BC4lean.KKTheory.GroupUniverseOddFirstParityProduct
