import BC4lean.CliffordEvenOddSourceCriterion
import BC4lean.GroupUniverseOddMoritaProductReduction

/-! # Actual signed even-by-odd compatibility across independent universes

The genuine coordinate product's plus range is transported as an entire
odd cycle. The actual completed tensor/sum Pauli unitary, all four creator
laws and localized positive lifts identify its signed source product.
The existing even-by-odd tensor route is retained by its proved coordinate
coherence, and the true signed-source law yields 101 associativity.
-/

noncomputable section
universe uΓ uA uB uC uD uE uF uG
namespace BC4lean.KKTheory.GroupUniverseOddSourceClass
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

set_option maxHeartbeats 8000000 in
/-- The original tensor Clifford even-by-odd product has its genuine
signed-source product value, with the full original module universes. -/
theorem sourceClass_evenOddProduct
    (x : KasparovHomotopyClass.{uΓ,uA,uB,uE} α β) (y : OddKK.{uΓ,uB,uC,uF} β γ) :
    sourceClass (GroupUniverseParityProduct.evenOddProduct x y) =
    GroupUniverseProduct.product (GroupUniverseExternalEvenClass.externalClass x) (sourceClass y) := by
  rw [← GroupUniverseOddFirstParityProduct.coordinateEvenOddProduct_eq_evenOddProduct]
  refine Quotient.inductionOn₂ x y ?_
  intro c d
  let cG := GroupUniverseEvenBase.ofEven c
  let dC := d.cliffordExpansion
  let R := GroupUniverseProduct.productOperator cG dC
  have hR : IsGradedKasparovProductOperator cG.cycle d.cycle.cliffordExpansion R :=
    GroupUniverseProduct.productOperator_isProduct cG dC
  let cX := BundledGradedKasparovCycle.of (CliffordExternalEvenCycle.cycle cG.cycle)
  let dS := BundledGradedKasparovCycle.of (CliffordOddSourceCycle.cycle d.cycle)
  change sourceClass (GroupUniverseCliffordCoordinateBridge.oddClass
      (GroupUniverseProduct.product
        (GroupUniverseEvenBridge.gradedClass (KasparovHomotopyClass.mk c))
        (GroupUniverseCliffordCoordinateBridge.gradedOddClass (OddKK.mk d)))) =
    GroupUniverseProduct.product
      (GroupUniverseExternalEvenClass.externalClass (KasparovHomotopyClass.mk c))
      (sourceClass (OddKK.mk d))
  rw [GroupUniverseEvenBridge.gradedClass_mk,
    GroupUniverseCliffordCoordinateBridge.gradedOddClass_mk, GroupUniverseProduct.product_mk,
    GroupUniverseExternalEvenClass.externalClass_mk, sourceClass_mk]
  change GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
      (CliffordOddSourceCycle.cycle (cliffordExtractOddCycle true
        (CliffordEvenOddCorner.rawCycle cG.cycle d.cycle R hR.cycleConditions)))) =
    GroupUniverseProduct.product (GradedKasparovHomotopyClass.mk cX)
      (GradedKasparovHomotopyClass.mk dS)
  calc
    _ = GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
        (CliffordOddSourceCycle.cycle (CliffordEvenOddSource.cornerCycle cG.cycle d.cycle R
          hR.cycleConditions))) :=
      GradedKasparovHomotopyClass.mk_eq_of_iso (CliffordOddSourceCycle.iso
        (CliffordEvenOddCorner.extractionIso cG.cycle d.cycle R hR.cycleConditions))
    _ = GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
        (gradedKasparovTensorCycleOfConditions cX.cycle dS.cycle
          (CliffordEvenOddSource.productOperator cG.cycle d.cycle R hR.cycleConditions)
          (CliffordEvenOddSource.isProduct cG.cycle d.cycle R hR).cycleConditions)) :=
      GradedKasparovHomotopyClass.mk_eq_of_iso
        (CliffordEvenOddSource.cycleIso cG.cycle d.cycle R hR.cycleConditions)
    _ = _ := (GroupUniverseProduct.product_mk_eq_of_isProduct cX dS
      (CliffordEvenOddSource.isProduct cG.cycle d.cycle R hR)).symm

end BC4lean.KKTheory.GroupUniverseOddSourceClass

namespace BC4lean.KKTheory.GroupUniverseOddFirstParityProduct
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

/-- Genuine 101 associativity follows from the actual signed-source product
law and genuine graded associativity, retaining all original universes. -/
theorem oddEvenOddProduct_assoc
    (x : OddKK.{uΓ,uA,uB,uE} α β) (y : KasparovHomotopyClass.{uΓ,uB,uC,uF} β γ)
    (z : OddKK.{uΓ,uC,uD,uG} γ η) :
    oddOddProduct (oddEvenProduct x y) z =
      oddOddProduct x (GroupUniverseParityProduct.evenOddProduct y z) := by
  apply GroupUniverseEvenBridge.gradedClass_injective
  rw [gradedClass_oddOddProduct_ulift, gradedOddClass_oddEvenProduct,
    gradedClass_oddOddProduct_ulift, GroupUniverseOddSourceClass.sourceClass_evenOddProduct]
  exact congrArg
    (GradedKasparovHomotopyClass.ulift.{uΓ,uA,uD,max (max uE uF) uG,uD})
    (GroupUniverseProduct.product_assoc (GroupUniverseCliffordCoordinateBridge.gradedOddClass x)
      (GroupUniverseExternalEvenClass.externalClass y) (GroupUniverseOddSourceClass.sourceClass z))

end BC4lean.KKTheory.GroupUniverseOddFirstParityProduct
