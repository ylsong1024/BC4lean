import BC4lean.KasparovDescentNativeClassCoherence
import BC4lean.KasparovDescentEvenProduct
import BC4lean.GroupUniverseEvenOddCoordinateCoherence
import BC4lean.GroupUniverseOddMoritaProductReduction
import BC4lean.GroupUniverseCommonParityProduct

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual native four-parity reduced descent product comparison



The products below are exactly the existing native even, tensor-Clifford,
Koszul external-even, and Pauli-row/column Morita products. The odd-odd proof
uses the existing genuine Morita reduction to the signed-source product;
no replacement product and no unproved crossed-matrix norm equality is used.
All bridge coherences come from actual saved whole-cycle tensor unitaries.

Group and all three coefficient universes remain independent. The explicit
common module universe is max(u,uΓ,uA,uB,uC), containing the actual crossed
coefficient carriers. The target acting group stays Unit at universe zero.
A variant starting with different arbitrary module universes needs explicit
coherence with the existing whole-module/full-interval universe comparison;
it is a separate packaging statement, not silently asserted here.
-/

noncomputable section
universe uΓ uA uB uC u
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C]
  (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B) (γ : CStarAlgebraAction Γ C)

/-- Actual native EO compatibility uses the genuine coordinate/tensor Clifford
coherence of the existing native product, and an injective whole odd bridge. -/
theorem oddClassHom_evenOddProduct
    (x : KasparovHomotopyClass.{uΓ,uA,uB,max u (max uΓ (max uA (max uB uC)))} α β) (y : OddKK.{uΓ,uB,uC,max u (max uΓ (max uA (max uB uC)))} β γ) :
    oddClassHom γ α (GroupUniverseParityProduct.evenOddProduct x y) =
      GroupUniverseParityProduct.evenOddProduct (evenClassHom β α x) (oddClassHom γ β y) := by
  change oddClass γ α (GroupUniverseParityProduct.evenOddProduct x y) =
    GroupUniverseParityProduct.evenOddProduct (evenClass β α x) (oddClass γ β y)
  apply GroupUniverseCliffordCoordinateBridge.gradedOddClass_injective
  calc
    GroupUniverseCliffordCoordinateBridge.gradedOddClass
        (oddClass γ α (GroupUniverseParityProduct.evenOddProduct x y)) =
        coordinateGradedClass α γ (GroupUniverseCliffordCoordinateBridge.gradedOddClass
          (GroupUniverseParityProduct.evenOddProduct x y)) :=
      (coordinateGradedClass_gradedOddClass α γ _).symm
    _ = coordinateGradedClass α γ (GroupUniverseProduct.product
        (GroupUniverseEvenBridge.gradedClass x)
        (GroupUniverseCliffordCoordinateBridge.gradedOddClass y)) := by
      rw [GroupUniverseOddFirstParityProduct.coordinateClass_evenOddProduct]
    _ = GroupUniverseProduct.product
        (evenGradedClass α β (GroupUniverseEvenBridge.gradedClass x))
        (coordinateGradedClass β γ (GroupUniverseCliffordCoordinateBridge.gradedOddClass y)) :=
      coordinateGradedClass_product_even_coordinate.{uΓ,uA,uB,uC,u} α β γ _ _
    _ = GroupUniverseProduct.product
        (GroupUniverseEvenBridge.gradedClass (evenClass β α x))
        (GroupUniverseCliffordCoordinateBridge.gradedOddClass (oddClass γ β y)) := by
      rw [evenGradedClass_gradedClass, coordinateGradedClass_gradedOddClass]
    _ = GroupUniverseCliffordCoordinateBridge.gradedOddClass
        (GroupUniverseParityProduct.evenOddProduct (evenClass β α x) (oddClass γ β y)) :=
      (GroupUniverseOddFirstParityProduct.coordinateClass_evenOddProduct _ _).symm

/-- Actual native OE compatibility follows its original coordinate/external
even construction. No injectivity of the signed-source map is assumed. -/
theorem oddClassHom_oddEvenProduct
    (x : OddKK.{uΓ,uA,uB,max u (max uΓ (max uA (max uB uC)))} α β) (y : KasparovHomotopyClass.{uΓ,uB,uC,max u (max uΓ (max uA (max uB uC)))} β γ) :
    oddClassHom γ α (GroupUniverseOddFirstParityProduct.oddEvenProduct x y) =
      GroupUniverseOddFirstParityProduct.oddEvenProduct (oddClassHom β α x) (evenClassHom γ β y) := by
  change oddClass γ α (GroupUniverseOddFirstParityProduct.oddEvenProduct x y) =
    GroupUniverseOddFirstParityProduct.oddEvenProduct (oddClass β α x) (evenClass γ β y)
  apply GroupUniverseCliffordCoordinateBridge.gradedOddClass_injective
  calc
    GroupUniverseCliffordCoordinateBridge.gradedOddClass
        (oddClass γ α (GroupUniverseOddFirstParityProduct.oddEvenProduct x y)) =
        coordinateGradedClass α γ (GroupUniverseCliffordCoordinateBridge.gradedOddClass
          (GroupUniverseOddFirstParityProduct.oddEvenProduct x y)) :=
      (coordinateGradedClass_gradedOddClass α γ _).symm
    _ = coordinateGradedClass α γ (GroupUniverseProduct.product
        (GroupUniverseCliffordCoordinateBridge.gradedOddClass x)
        (GroupUniverseExternalEvenClass.externalClass y)) := by
      rw [GroupUniverseOddFirstParityProduct.gradedOddClass_oddEvenProduct]
    _ = GroupUniverseProduct.product
        (coordinateGradedClass α β (GroupUniverseCliffordCoordinateBridge.gradedOddClass x))
        (externalGradedClass β γ (GroupUniverseExternalEvenClass.externalClass y)) :=
      coordinateGradedClass_product_coordinate_external.{uΓ,uA,uB,uC,u} α β γ _ _
    _ = GroupUniverseProduct.product
        (GroupUniverseCliffordCoordinateBridge.gradedOddClass (oddClass β α x))
        (GroupUniverseExternalEvenClass.externalClass (evenClass γ β y)) := by
      rw [coordinateGradedClass_gradedOddClass, externalGradedClass_externalClass]
    _ = GroupUniverseCliffordCoordinateBridge.gradedOddClass
        (GroupUniverseOddFirstParityProduct.oddEvenProduct (oddClass β α x) (evenClass γ β y)) :=
      (GroupUniverseOddFirstParityProduct.gradedOddClass_oddEvenProduct _ _).symm

/-- Actual native OO compatibility uses the already proved genuine row/column
Morita reduction. The common module universe contains the final coefficient
universe on both sides, so the actual whole-module lift reduces as proved by
that theorem, rather than being erased by an unsupported type identification. -/
theorem evenClassHom_oddOddProduct
    (x : OddKK.{uΓ,uA,uB,max u (max uΓ (max uA (max uB uC)))} α β) (y : OddKK.{uΓ,uB,uC,max u (max uΓ (max uA (max uB uC)))} β γ) :
    evenClassHom γ α (GroupUniverseOddFirstParityProduct.oddOddProduct x y) =
      GroupUniverseOddFirstParityProduct.oddOddProduct (oddClassHom β α x) (oddClassHom γ β y) := by
  change evenClass γ α (GroupUniverseOddFirstParityProduct.oddOddProduct x y) =
    GroupUniverseOddFirstParityProduct.oddOddProduct (oddClass β α x) (oddClass γ β y)
  apply GroupUniverseEvenBridge.gradedClass_injective
  calc
    GroupUniverseEvenBridge.gradedClass
        (evenClass γ α (GroupUniverseOddFirstParityProduct.oddOddProduct x y)) =
        evenGradedClass α γ (GroupUniverseEvenBridge.gradedClass
          (GroupUniverseOddFirstParityProduct.oddOddProduct x y)) :=
      (evenGradedClass_gradedClass α γ _).symm
    _ = evenGradedClass α γ (GroupUniverseProduct.product
        (GroupUniverseCliffordCoordinateBridge.gradedOddClass x)
        (GroupUniverseOddSourceClass.sourceClass y)) := by
      rw [GroupUniverseOddFirstParityProduct.gradedClass_oddOddProduct.{uΓ,uA,uB,uC,max u (max uΓ (max uA (max uB uC))),max u (max uΓ (max uA (max uB uC)))}]
    _ = GroupUniverseProduct.product
        (coordinateGradedClass α β (GroupUniverseCliffordCoordinateBridge.gradedOddClass x))
        (signedGradedClass β γ (GroupUniverseOddSourceClass.sourceClass y)) :=
      evenGradedClass_product_coordinate_signed.{uΓ,uA,uB,uC,u} α β γ _ _
    _ = GroupUniverseProduct.product
        (GroupUniverseCliffordCoordinateBridge.gradedOddClass (oddClass β α x))
        (GroupUniverseOddSourceClass.sourceClass (oddClass γ β y)) := by
      rw [coordinateGradedClass_gradedOddClass, signedGradedClass_sourceClass]
    _ = GroupUniverseEvenBridge.gradedClass
        (GroupUniverseOddFirstParityProduct.oddOddProduct (oddClass β α x) (oddClass γ β y)) :=
      (GroupUniverseOddFirstParityProduct.gradedClass_oddOddProduct.{0,max uΓ uA,max uΓ uB,max uΓ uC,max u (max uΓ (max uA (max uB uC))),max u (max uΓ (max uA (max uB uC)))} _ _).symm

/-- The saved actual parity-wise class homomorphism preserves all four
branches of the existing common-universe native product. -/
theorem classHom_product (p q : Bool)
    (x : GroupUniverseParityGroup.KKParityGroup.{uΓ,uA,uB,max u (max uΓ (max uA (max uB uC)))} p α β)
    (y : GroupUniverseParityGroup.KKParityGroup.{uΓ,uB,uC,max u (max uΓ (max uA (max uB uC)))} q β γ) :
    classHom γ α (Bool.xor p q)
        (GroupUniverseCommonParityProduct.product.{uΓ,uA,uB,uC,max u uΓ} p q x y) =
      GroupUniverseCommonParityProduct.product.{0,max uΓ uA,max uΓ uB,max uΓ uC,u} p q
        (classHom β α p x) (classHom γ β q y) := by
  cases p <;> cases q
  · exact evenClassHom_evenProduct.{uΓ,uA,uB,uC,u} α β γ x y
  · exact oddClassHom_evenOddProduct.{uΓ,uA,uB,uC,u} α β γ x y
  · exact oddClassHom_oddEvenProduct.{uΓ,uA,uB,uC,u} α β γ x y
  · exact evenClassHom_oddOddProduct.{uΓ,uA,uB,uC,u} α β γ x y

end BC4lean.KKTheory.KasparovDescent
