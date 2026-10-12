import BC4lean.CliffordExternalEvenMonoidalPositivity
import BC4lean.GroupUniverseExternalEvenClass
import BC4lean.GroupUniverseParityProduct
import BC4lean.GroupUniverseOddFirstParityProduct

/-! # Proved external even multiplicativity at independent universes

The actual completed Koszul tensor unitary transports the whole product
criterion, including all four connection laws and localized positive
lifts. Genuine full uniqueness gives the quotient law. The resulting
odd-even-even associativity, and two further mixed parity laws, use the
actual graded associativity witness and faithful quotient bridges.
-/

noncomputable section
universe uΓ uA uB uC uD uE uF uG
namespace BC4lean.KKTheory.GroupUniverseExternalEvenClass
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C] [Countable Γ]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

theorem externalClass_evenProduct (x : KasparovHomotopyClass.{uΓ,uA,uB,uE} α β)
    (y : KasparovHomotopyClass.{uΓ,uB,uC,uF} β γ) :
    externalClass (GroupUniverseParityProduct.evenProduct x y) =
      GroupUniverseProduct.product (externalClass x) (externalClass y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro c d
  let cG := GroupUniverseEvenBase.ofEven c
  let dG := GroupUniverseEvenBase.ofEven d
  let R := GroupUniverseProduct.productOperator cG dG
  have hR : IsGradedKasparovProductOperator cG.cycle dG.cycle R :=
    GroupUniverseProduct.productOperator_isProduct cG dG
  let cX := BundledGradedKasparovCycle.of (CliffordExternalEvenCycle.cycle cG.cycle)
  let dX := BundledGradedKasparovCycle.of (CliffordExternalEvenCycle.cycle dG.cycle)
  simp only [GroupUniverseParityProduct.evenProduct]
  change GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
      (CliffordExternalEvenMonoidal.externalTensorCycle cG.cycle dG.cycle R hR.cycleConditions)) =
    GroupUniverseProduct.product (GradedKasparovHomotopyClass.mk cX) (GradedKasparovHomotopyClass.mk dX)
  calc
    _ = GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
        (gradedKasparovTensorCycleOfConditions cX.cycle dX.cycle
          (CliffordExternalEvenMonoidal.productOperator dG.cycle R)
          (CliffordExternalEvenMonoidal.isProduct cG.cycle dG.cycle R hR).cycleConditions)) :=
      GradedKasparovHomotopyClass.mk_eq_of_iso
        (CliffordExternalEvenMonoidal.cycleIso cG.cycle dG.cycle R hR.cycleConditions)
    _ = _ := (GroupUniverseProduct.product_mk_eq_of_isProduct cX dX
      (CliffordExternalEvenMonoidal.isProduct cG.cycle dG.cycle R hR)).symm

end BC4lean.KKTheory.GroupUniverseExternalEvenClass

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
open GroupUniverseCliffordCoordinateBridge

theorem oddEvenEvenProduct_assoc (x : OddKK.{uΓ,uA,uB,uE} α β)
    (y : KasparovHomotopyClass.{uΓ,uB,uC,uF} β γ)
    (z : KasparovHomotopyClass.{uΓ,uC,uD,uG} γ η) :
    oddEvenProduct (oddEvenProduct x y) z =
      oddEvenProduct x (GroupUniverseParityProduct.evenProduct y z) := by
  apply gradedOddClass_injective
  simp only [gradedOddClass_oddEvenProduct, GroupUniverseExternalEvenClass.externalClass_evenProduct]
  exact GroupUniverseProduct.product_assoc _ _ _

theorem coordinateEvenOddEvenProduct_assoc
    (x : KasparovHomotopyClass.{uΓ,uA,uB,uE} α β) (y : OddKK.{uΓ,uB,uC,uF} β γ)
    (z : KasparovHomotopyClass.{uΓ,uC,uD,uG} γ η) :
    oddEvenProduct (coordinateEvenOddProduct x y) z =
      coordinateEvenOddProduct x (oddEvenProduct y z) := by
  apply gradedOddClass_injective
  simp only [gradedOddClass_oddEvenProduct, gradedOddClass_coordinateEvenOddProduct]
  exact GroupUniverseProduct.product_assoc _ _ _

theorem coordinateEvenEvenOddProduct_assoc
    (x : KasparovHomotopyClass.{uΓ,uA,uB,uE} α β)
    (y : KasparovHomotopyClass.{uΓ,uB,uC,uF} β γ) (z : OddKK.{uΓ,uC,uD,uG} γ η) :
    coordinateEvenOddProduct (GroupUniverseParityProduct.evenProduct x y) z =
      coordinateEvenOddProduct x (coordinateEvenOddProduct y z) := by
  apply gradedOddClass_injective
  simp only [gradedOddClass_coordinateEvenOddProduct, GroupUniverseParityProduct.gradedClass_evenProduct]
  exact GroupUniverseProduct.product_assoc _ _ _

end BC4lean.KKTheory.GroupUniverseOddFirstParityProduct
