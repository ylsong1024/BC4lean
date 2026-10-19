import BC4lean.KasparovDescentGradedClass
import BC4lean.KasparovDescentGradedProductClass

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The actual graded full-homotopy descent map preserves the existing product

The imported class map is
constructed from the actual arbitrary full graded interval homotopy transport.
The product proof uses actual representative product criterion and uniqueness,
not a compatibility field or a conditional desired conclusion.

Group and coefficient universes are independent. The original modules use
the common covering universe max(u,uΓ,uA,uB,uC). Target Unit stays at zero
through the existing independent-universe product API. Comparison of inputs
in different arbitrary module universes remains a separate packaging step.
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
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}
  (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B) (γ : CStarAlgebraAction Γ C)
  (hα : α.PreservesGrading δA) (hβ : β.PreservesGrading δB) (hγ : γ.PreservesGrading δC)

/-- The genuine graded quotient descent respects the existing product on
full homotopy classes, by actual product representatives and full uniqueness. -/
theorem gradedClass_product
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,max u (max uΓ (max uA (max uB uC)))} α β δA δB)
    (y : GradedKasparovHomotopyClass.{uΓ,uB,uC,max u (max uΓ (max uA (max uB uC)))} β γ δB δC) :
    gradedClass γ α hα hγ (GroupUniverseProduct.product x y) =
      GroupUniverseProduct.product (gradedClass β α hα hβ x) (gradedClass γ β hβ hγ y) := by
  refine Quotient.inductionOn₂' x y ?_
  intro c d
  change gradedClass γ α hα hγ
      (GroupUniverseProduct.product (GradedKasparovHomotopyClass.mk c)
        (GradedKasparovHomotopyClass.mk d)) =
    GroupUniverseProduct.product
      (gradedClass β α hα hβ (GradedKasparovHomotopyClass.mk c))
      (gradedClass γ β hβ hγ (GradedKasparovHomotopyClass.mk d))
  rw [GroupUniverseProduct.product_mk, gradedClass_mk, gradedClass_mk, gradedClass_mk]
  exact (graded_product_class.{uΓ,uA,uB,uC,u} α β γ c d).symm

end BC4lean.KKTheory.KasparovDescent
