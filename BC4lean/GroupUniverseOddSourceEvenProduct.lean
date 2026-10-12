import BC4lean.GroupUniverseOddSourceClass
import BC4lean.CliffordOddSourceEvenCriterion
import BC4lean.GroupUniverseOddFirstParityProduct
import BC4lean.GroupUniverseMatrixMoritaProduct

/-! # Actual signed-source compatibility with odd-by-even products

The original chosen product's actual positive coefficient corner is
extracted as an entire odd cycle. Its signed source is carried by the
completed tensor/sum and quarter-phase unitaries to a genuine product
cycle. The raw proof supplies all four creators and localized positive
lifts; actual full uniqueness proves this law across independent universes.
-/

noncomputable section
universe uΓ uA uB uC uE uF
namespace BC4lean.KKTheory.GroupUniverseOddSourceClass
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

set_option maxHeartbeats 8000000 in
theorem sourceClass_oddEvenProduct
    (x : OddKK.{uΓ,uA,uB,uE} α β) (y : KasparovHomotopyClass.{uΓ,uB,uC,uF} β γ) :
    sourceClass (GroupUniverseOddFirstParityProduct.oddEvenProduct x y) =
      GroupUniverseProduct.product (sourceClass x) (GroupUniverseEvenBridge.gradedClass y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro c d
  let dG := GroupUniverseEvenBase.ofEven d
  let dX := BundledGradedKasparovCycle.of (CliffordExternalEvenCycle.cycle dG.cycle)
  let R := GroupUniverseProduct.productOperator c.cliffordExpansion dX
  have hR : IsGradedKasparovProductOperator c.cycle.cliffordExpansion
      (CliffordExternalEvenCycle.cycle dG.cycle) R :=
    GroupUniverseProduct.productOperator_isProduct c.cliffordExpansion dX
  let cS := BundledGradedKasparovCycle.of (CliffordOddSourceCycle.cycle c.cycle)
  change sourceClass (GroupUniverseCliffordCoordinateBridge.oddClass
      (GroupUniverseProduct.product
        (GroupUniverseCliffordCoordinateBridge.gradedOddClass (OddKK.mk c))
        (GroupUniverseExternalEvenClass.externalClass (KasparovHomotopyClass.mk d)))) =
    GroupUniverseProduct.product (sourceClass (OddKK.mk c))
      (GroupUniverseEvenBridge.gradedClass (KasparovHomotopyClass.mk d))
  rw [GroupUniverseCliffordCoordinateBridge.gradedOddClass_mk,
    GroupUniverseExternalEvenClass.externalClass_mk, GroupUniverseProduct.product_mk,
    sourceClass_mk, GroupUniverseEvenBridge.gradedClass_mk]
  change GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
      (CliffordOddSourceCycle.cycle (cliffordExtractOddCycle true
        (CliffordOddEvenCorner.rawCycle c.cycle dG.cycle R hR.cycleConditions)))) =
    GroupUniverseProduct.product (GradedKasparovHomotopyClass.mk cS)
      (GradedKasparovHomotopyClass.mk dG)
  calc
    _ = GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
        (CliffordOddSourceCycle.cycle (CliffordOddSourceEven.cornerCycle c.cycle dG.cycle R
          hR.cycleConditions))) :=
      GradedKasparovHomotopyClass.mk_eq_of_iso (CliffordOddSourceCycle.iso
        (CliffordOddEvenCorner.extractionIso c.cycle dG.cycle R hR.cycleConditions))
    _ = GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
        (gradedKasparovTensorCycleOfConditions cS.cycle dG.cycle
          (CliffordOddSourceEven.productOperator c.cycle dG.cycle R hR.cycleConditions)
          (CliffordOddSourceEven.isProduct c.cycle dG.cycle R hR).cycleConditions)) :=
      GradedKasparovHomotopyClass.mk_eq_of_iso
        (CliffordOddSourceEven.cycleIso c.cycle dG.cycle R hR.cycleConditions)
    _ = _ := (GroupUniverseProduct.product_mk_eq_of_isProduct cS dG
      (CliffordOddSourceEven.isProduct c.cycle dG.cycle R hR)).symm

omit [Countable Γ] [TopologicalSpace.SeparableSpace A] in
theorem coordinateClass_eq_toMatrixClass (x : OddKK.{uΓ,uA,uC,uE} α γ) :
    GroupUniverseExternalOddClass.coordinateClass x =
      GroupUniverseMatrixMoritaBridge.toMatrixClass (sourceClass x) := by
  refine Quotient.inductionOn x ?_
  intro c
  rfl

/-- The genuine row extension also preserves this actual product, by its
proved full tensor criterion and the preceding signed-source law. -/
theorem coordinateClass_oddEvenProduct
    (x : OddKK.{uΓ,uA,uB,uE} α β) (y : KasparovHomotopyClass.{uΓ,uB,uC,uF} β γ) :
    GroupUniverseExternalOddClass.coordinateClass
      (GroupUniverseOddFirstParityProduct.oddEvenProduct x y) =
    GroupUniverseProduct.product (sourceClass x)
      (GroupUniverseMatrixMoritaBridge.toMatrixClass (GroupUniverseEvenBridge.gradedClass y)) := by
  rw [coordinateClass_eq_toMatrixClass, sourceClass_oddEvenProduct]
  exact GroupUniverseMatrixMoritaProduct.toMatrixClass_product γ _ _

end BC4lean.KKTheory.GroupUniverseOddSourceClass
