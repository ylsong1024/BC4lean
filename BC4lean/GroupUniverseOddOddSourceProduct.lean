import BC4lean.CliffordOddOddSourceCriterion
import BC4lean.CliffordExternalEvenCycleIso
import BC4lean.GroupUniverseEvenOddSourceProduct

/-! # Genuine three-odd coherence at the actual common module universe

The existing matrix Morita product has its proved signed-source value.
The completed matching-coordinate tensor unitary and explicit Pauli
Fourier unitary identify its external even cycle with the other Clifford
placement. All four creator laws and localized positive lifts are proved
in the raw criterion. Genuine full uniqueness gives the quotient law;
genuine graded associativity then gives 111 for independent coefficients.
-/

noncomputable section
universe uΓ uA uB uC uD uE
namespace BC4lean.KKTheory.GroupUniverseOddFirstParityProduct
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

set_option maxHeartbeats 8000000 in
/-- The actual external even image of the matrix Morita product is the
genuine signed-first, Clifford-second product. The chosen module universe
contains `uC`, as required by the actual row and column tensors. -/
theorem externalClass_oddOddProduct
    (x : OddKK.{uΓ,uA,uB,max uE uC} α β) (y : OddKK.{uΓ,uB,uC,max uE uC} β γ) :
    GroupUniverseExternalEvenClass.externalClass (oddOddProduct x y) =
      GroupUniverseProduct.product (GroupUniverseOddSourceClass.sourceClass x)
        (GroupUniverseCliffordCoordinateBridge.gradedOddClass y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro c d
  let dS := BundledGradedKasparovCycle.of (CliffordOddSourceCycle.cycle d.cycle)
  let R := GroupUniverseProduct.productOperator c.cliffordExpansion dS
  have hR : IsGradedKasparovProductOperator c.cycle.cliffordExpansion
      (CliffordOddSourceCycle.cycle d.cycle) R :=
    GroupUniverseProduct.productOperator_isProduct c.cliffordExpansion dS
  let cS := BundledGradedKasparovCycle.of (CliffordOddSourceCycle.cycle c.cycle)
  have hp : oddOddProduct (OddKK.mk c) (OddKK.mk d) =
      GroupUniverseEvenBridge.evenClass (GroupUniverseProduct.product
        (GroupUniverseCliffordCoordinateBridge.gradedOddClass (OddKK.mk c))
        (GroupUniverseOddSourceClass.sourceClass (OddKK.mk d))) := by
    apply GroupUniverseEvenBridge.gradedClass_injective
    rw [gradedClass_oddOddProduct, GroupUniverseEvenBridge.gradedClass_evenClass]
  change GroupUniverseExternalEvenClass.externalClass
      (oddOddProduct (OddKK.mk c) (OddKK.mk d)) =
    GroupUniverseProduct.product (GroupUniverseOddSourceClass.sourceClass (OddKK.mk c))
      (GroupUniverseCliffordCoordinateBridge.gradedOddClass (OddKK.mk d))
  rw [hp]
  simp only [GroupUniverseCliffordCoordinateBridge.gradedOddClass_mk,
    GroupUniverseOddSourceClass.sourceClass_mk, GroupUniverseProduct.product_mk,
    GroupUniverseEvenBridge.evenClass_mk, GroupUniverseExternalEvenClass.externalClass_mk,
    GroupUniverseEvenBase.toEven]
  change GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
      (CliffordExternalEvenCycle.cycle (CliffordOddOddCoordinate.rawCycle c.cycle d.cycle R
        hR.cycleConditions))) =
    GroupUniverseProduct.product (GradedKasparovHomotopyClass.mk cS)
      (GradedKasparovHomotopyClass.mk d.cliffordExpansion)
  calc
    _ = GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
        (CliffordOddOddSource.externalCycle c.cycle d.cycle R hR.cycleConditions)) :=
      GradedKasparovHomotopyClass.mk_eq_of_iso (CliffordExternalEvenCycle.iso
        (CliffordOddOddCoordinate.cycleIso c.cycle d.cycle R hR.cycleConditions))
    _ = GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
        (gradedKasparovTensorCycleOfConditions cS.cycle d.cliffordExpansion.cycle
          (CliffordOddOddSource.productOperator c.cycle d.cycle R hR.cycleConditions)
          (CliffordOddOddSource.isProduct c.cycle d.cycle R hR).cycleConditions)) :=
      GradedKasparovHomotopyClass.mk_eq_of_iso
        (CliffordOddOddSource.cycleIso c.cycle d.cycle R hR.cycleConditions)
    _ = _ := (GroupUniverseProduct.product_mk_eq_of_isProduct cS d.cliffordExpansion
      (CliffordOddOddSource.isProduct c.cycle d.cycle R hR)).symm

variable {D : Type uD} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [TopologicalSpace.SeparableSpace D] {η : CStarAlgebraAction Γ D}

/-- Genuine 111 associativity at the common actual module universe which
contains both distinct intermediate coefficient universes. -/
theorem oddOddOddProduct_assoc
    (x : OddKK.{uΓ,uA,uB,max uE (max uC uD)} α β)
    (y : OddKK.{uΓ,uB,uC,max uE (max uC uD)} β γ)
    (z : OddKK.{uΓ,uC,uD,max uE (max uC uD)} γ η) :
    GroupUniverseParityProduct.evenOddProduct (oddOddProduct x y) z =
      oddEvenProduct x (oddOddProduct y z) := by
  apply GroupUniverseCliffordCoordinateBridge.gradedOddClass_injective
  rw [coordinateClass_evenOddProduct,
    gradedClass_oddOddProduct.{uΓ,uA,uB,uC,max uE uD,max uE uD},
    gradedOddClass_oddEvenProduct,
    externalClass_oddOddProduct.{uΓ,uB,uC,uD,max uE uC}]
  exact GroupUniverseProduct.product_assoc (GroupUniverseCliffordCoordinateBridge.gradedOddClass x)
    (GroupUniverseOddSourceClass.sourceClass y)
    (GroupUniverseCliffordCoordinateBridge.gradedOddClass z)

end BC4lean.KKTheory.GroupUniverseOddFirstParityProduct
