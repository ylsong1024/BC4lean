import BC4lean.KasparovDescentGradedProduct
import BC4lean.GroupUniverseProduct

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Comparison with the existing genuine product class

This uses the existing
actual graded product on full arbitrary-module homotopy classes and its
actual product-operator uniqueness theorem. No replacement product operation
is defined. The statements compare actual raw descended representatives.
The existing independent-universe product API keeps Unit at universe zero
while the crossed algebras and carriers remain in their actual universe.
A well-defined descent map on full homotopy classes remains a separate
construction, as do native parity/Clifford/Morita identification laws.
-/

noncomputable section
universe uΓ uA uB uC u
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC}
  {E F : Type (max u (max uΓ (max uA (max uB uC))))} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F]
  [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
  [Countable Γ] [TopologicalSpace.SeparableSpace A]
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C]
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}
  (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B) (γ : CStarAlgebraAction Γ C)
  (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)
  (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation))

/-- Every actual original product representative descends to the existing
product class of the two actual descended representatives. The class equality
uses actual product uniqueness plus the constructed whole-cycle isomorphism. -/
theorem graded_product_class_of_isProduct
    (hR : IsGradedKasparovProductOperator c d R) :
    GroupUniverseProduct.product
      (GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of (gradedCycle β α c)))
      (GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of (gradedCycle γ β d))) =
    GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
      (gradedCycle γ α (gradedKasparovTensorCycleOfConditions c d R hR.cycleConditions))) := by
  have hDesc := descended_isGradedProduct α β γ c d R hR
  have hchoice := GroupUniverseProduct.product_mk_eq_of_isProduct
    (BundledGradedKasparovCycle.of (gradedCycle β α c))
    (BundledGradedKasparovCycle.of (gradedCycle γ β d)) hDesc
  have hiso := GradedKasparovHomotopyClass.mk_eq_of_iso
    (c := BundledGradedKasparovCycle.of
      (gradedCycle γ α (gradedKasparovTensorCycleOfConditions c d R hR.cycleConditions)))
    (d := BundledGradedKasparovCycle.of
      (gradedKasparovTensorCycleOfConditions (gradedCycle β α c) (gradedCycle γ β d)
        (descendedConnectionOperator β γ d.groupAction d.representation d.representation_equivariant R)
        hDesc.cycleConditions))
    (descended_product_cycleIso α β γ c d R hR.cycleConditions)
  exact hchoice.trans hiso.symm

/-- In particular the existing chosen original product has the same descended
class as the existing product of the two raw descended classes. This invokes
the already genuine original existence/uniqueness implementation. -/
theorem graded_product_class
    (c₀ : BundledGradedKasparovCycle.{uΓ,uA,uB,max u (max uΓ (max uA (max uB uC)))} α β δA δB)
    (d₀ : BundledGradedKasparovCycle.{uΓ,uB,uC,max u (max uΓ (max uA (max uB uC)))} β γ δB δC) :
    GroupUniverseProduct.product
      (GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of (gradedCycle β α c₀.cycle)))
      (GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of (gradedCycle γ β d₀.cycle))) =
    GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
      (gradedCycle γ α (GroupUniverseProduct.bundledProduct c₀ d₀).cycle)) := by
  dsimp only [GroupUniverseProduct.bundledProduct]
  exact graded_product_class_of_isProduct.{uΓ,uA,uB,uC,u}
    (E := c₀.carrier) (F := d₀.carrier) α β γ c₀.cycle d₀.cycle
    (GroupUniverseProduct.productOperator c₀ d₀) (GroupUniverseProduct.productOperator_isProduct c₀ d₀)

end BC4lean.KKTheory.KasparovDescent
