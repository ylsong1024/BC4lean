import BC4lean.KasparovDescentEvenGradedCoherence
import BC4lean.KasparovDescentNativeClassCoherence
import BC4lean.KasparovDescentGradedProductClass
import BC4lean.KasparovDescentClass
import BC4lean.GroupUniverseParityProduct

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual native even-even reduced product compatibility

This uses the saved genuine
even full-homotopy class map, actual trivial-grading coherence, the genuine
crossed product criterion, and the EXISTING independent-universe product.
No product compatibility premise is supplied. Odd native branches require
separate concrete Clifford and matrix-Morita coherence.

Group and coefficient universes remain independent. Both original module
carriers lie in the explicit common universe max(u,uΓ,uA,uB,uC), containing
all actual crossed coefficient carriers. The target group remains Unit in
universe zero through the existing GroupUniverse APIs. Inputs in different
arbitrary module universes need an explicit whole-module comparison.
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

omit [TopologicalSpace.SeparableSpace A] in
/-- Actual trivial-grading index transport identifies the raw graded descent
class with the graded image of the genuine native even descent class. -/
theorem regrade_descent_toEven_class
    (c : BundledGradedKasparovCycle.{uΓ,uA,uB,u} α β CStarGrading.trivial CStarGrading.trivial) :
    GradedKasparovHomotopyClass.regrade
      (reducedCrossedProductGrading_trivial α) (reducedCrossedProductGrading_trivial β)
      (GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of (gradedCycle β α c.cycle))) =
    GroupUniverseEvenBridge.gradedClass
      (evenClass β α (KasparovHomotopyClass.mk (GroupUniverseEvenBase.toEven c))) := by
  rw [GradedKasparovHomotopyClass.regrade_mk, evenClass_mk,
    GroupUniverseEvenBridge.gradedClass_mk]
  exact GradedKasparovHomotopyClass.mk_eq_of_iso (toEvenDescentIso β α c.cycle)

/-- The saved genuine even class homomorphism preserves the project's actual
native even-even product, by product uniqueness and the concrete bridge iso. -/
theorem evenClassHom_evenProduct
    (x : KasparovHomotopyClass.{uΓ,uA,uB,max u (max uΓ (max uA (max uB uC)))} α β)
    (y : KasparovHomotopyClass.{uΓ,uB,uC,max u (max uΓ (max uA (max uB uC)))} β γ) :
    evenClassHom γ α (GroupUniverseParityProduct.evenProduct x y) =
      GroupUniverseParityProduct.evenProduct (evenClassHom β α x) (evenClassHom γ β y) := by
  change evenClass γ α (GroupUniverseParityProduct.evenProduct x y) =
    GroupUniverseParityProduct.evenProduct (evenClass β α x) (evenClass γ β y)
  apply GroupUniverseEvenBridge.gradedClass_injective
  calc
    GroupUniverseEvenBridge.gradedClass
        (evenClass γ α (GroupUniverseParityProduct.evenProduct x y)) =
        evenGradedClass α γ (GroupUniverseEvenBridge.gradedClass
          (GroupUniverseParityProduct.evenProduct x y)) :=
      (evenGradedClass_gradedClass α γ _).symm
    _ = evenGradedClass α γ (GroupUniverseProduct.product
        (GroupUniverseEvenBridge.gradedClass x) (GroupUniverseEvenBridge.gradedClass y)) := by
      rw [GroupUniverseParityProduct.gradedClass_evenProduct]
    _ = GroupUniverseProduct.product
        (evenGradedClass α β (GroupUniverseEvenBridge.gradedClass x))
        (evenGradedClass β γ (GroupUniverseEvenBridge.gradedClass y)) :=
      evenGradedClass_product.{uΓ,uA,uB,uC,u} α β γ _ _
    _ = GroupUniverseProduct.product
        (GroupUniverseEvenBridge.gradedClass (evenClass β α x))
        (GroupUniverseEvenBridge.gradedClass (evenClass γ β y)) := by
      rw [evenGradedClass_gradedClass, evenGradedClass_gradedClass]
    _ = GroupUniverseEvenBridge.gradedClass
        (GroupUniverseParityProduct.evenProduct (evenClass β α x) (evenClass γ β y)) :=
      (GroupUniverseParityProduct.gradedClass_evenProduct _ _).symm

end BC4lean.KKTheory.KasparovDescent
