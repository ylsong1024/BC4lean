import BC4lean.KasparovDescentGradedClassProduct
import BC4lean.KasparovDescentPairCoefficientEquiv
import BC4lean.GradedKasparovRegrade

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual graded class transports used by the native parity branches

These are definitions using the constructed
graded descent map, actual crossed pair equivalence, and equality of crossed
trivial gradings. Four product laws below follow from actual graded descent
product compatibility and the EXISTING coefficient/source product transport.
No native parity coherence or desired product law is an input hypothesis.
-/

noncomputable section
universe uΓ uA uB uC uE u
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C]
  (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B) (γ : CStarAlgebraAction Γ C)

/-- Ordinary trivial/trivial graded descent, with its proved grading indices. -/
def evenGradedClass
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β CStarGrading.trivial CStarGrading.trivial) :=
  GradedKasparovHomotopyClass.regrade
    (reducedCrossedProductGrading_trivial α) (reducedCrossedProductGrading_trivial β)
    (gradedClass β α α.preservesGrading_trivial β.preservesGrading_trivial x)

/-- Coordinate Clifford final coefficient descent through the actual pair equivalence. -/
def coordinateGradedClass
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading) :=
  GradedKasparovHomotopyClass.regrade (reducedCrossedProductGrading_trivial α) rfl
    (KasparovDescentPairCoefficientEquiv.changeCoefficients β
      (gradedClass (cliffordCoefficientAction β) α α.preservesGrading_trivial
        (cliffordCoefficientAction_preservesGrading β) x))

/-- Signed Clifford source descent by actual inverse-pair source pullback. -/
def signedGradedClass
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} (cliffordCoefficientAction α) β
      cliffordCoefficientGrading CStarGrading.trivial) :=
  GradedKasparovHomotopyClass.regrade rfl (reducedCrossedProductGrading_trivial β)
    (KasparovDescentPairCoefficientEquiv.sourcePullback α
      (gradedClass β (cliffordCoefficientAction α) (cliffordCoefficientAction_preservesGrading α)
        β.preservesGrading_trivial x))

/-- Both actual Clifford source and coefficient changes for the external even cycle. -/
def externalGradedClass
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} (cliffordCoefficientAction α)
      (cliffordCoefficientAction β) cliffordCoefficientGrading cliffordCoefficientGrading) :=
  KasparovDescentPairCoefficientEquiv.sourcePullback α
    (KasparovDescentPairCoefficientEquiv.changeCoefficients β
      (gradedClass (cliffordCoefficientAction β) (cliffordCoefficientAction α)
        (cliffordCoefficientAction_preservesGrading α)
        (cliffordCoefficientAction_preservesGrading β) x))

/-- Actual plain graded product transport, not a native product assertion. -/
theorem evenGradedClass_product
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,max u (max uΓ (max uA (max uB uC)))} α β CStarGrading.trivial CStarGrading.trivial)
    (y : GradedKasparovHomotopyClass.{uΓ,uB,uC,max u (max uΓ (max uA (max uB uC)))} β γ CStarGrading.trivial CStarGrading.trivial) :
    evenGradedClass α γ (GroupUniverseProduct.product x y) =
      GroupUniverseProduct.product (evenGradedClass α β x) (evenGradedClass β γ y) := by
  unfold evenGradedClass
  rw [gradedClass_product.{uΓ,uA,uB,uC,u} α β γ α.preservesGrading_trivial
    β.preservesGrading_trivial γ.preservesGrading_trivial]
  exact GradedKasparovHomotopyClass.regrade_product
    (reducedCrossedProductGrading_trivial α) (reducedCrossedProductGrading_trivial β)
    (reducedCrossedProductGrading_trivial γ) _ _

/-- Actual final Clifford coefficient transport of an even-coordinate product. -/
theorem coordinateGradedClass_product_even_coordinate
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,max u (max uΓ (max uA (max uB uC)))} α β CStarGrading.trivial CStarGrading.trivial)
    (y : GradedKasparovHomotopyClass.{uΓ,uB,uC,max u (max uΓ (max uA (max uB uC)))} β (cliffordCoefficientAction γ)
      CStarGrading.trivial cliffordCoefficientGrading) :
    coordinateGradedClass α γ (GroupUniverseProduct.product x y) =
      GroupUniverseProduct.product (evenGradedClass α β x) (coordinateGradedClass β γ y) := by
  unfold coordinateGradedClass evenGradedClass
  rw [gradedClass_product.{uΓ,uA,uB,uC,u} α β (cliffordCoefficientAction γ) α.preservesGrading_trivial
    β.preservesGrading_trivial (cliffordCoefficientAction_preservesGrading γ), KasparovDescentPairCoefficientEquiv.changeCoefficients_product γ (fun _ _ => rfl)]
  exact GradedKasparovHomotopyClass.regrade_product
    (reducedCrossedProductGrading_trivial α) (reducedCrossedProductGrading_trivial β) rfl _ _

/-- Actual intermediate/final pair transport of a coordinate-external product. -/
theorem coordinateGradedClass_product_coordinate_external
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,max u (max uΓ (max uA (max uB uC)))} α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading)
    (y : GradedKasparovHomotopyClass.{uΓ,uB,uC,max u (max uΓ (max uA (max uB uC)))} (cliffordCoefficientAction β)
      (cliffordCoefficientAction γ) cliffordCoefficientGrading cliffordCoefficientGrading) :
    coordinateGradedClass α γ (GroupUniverseProduct.product x y) =
      GroupUniverseProduct.product (coordinateGradedClass α β x) (externalGradedClass β γ y) := by
  unfold coordinateGradedClass externalGradedClass
  rw [gradedClass_product.{uΓ,uA,uB,uC,u} α (cliffordCoefficientAction β) (cliffordCoefficientAction γ)
    α.preservesGrading_trivial (cliffordCoefficientAction_preservesGrading β)
    (cliffordCoefficientAction_preservesGrading γ), KasparovDescentPairCoefficientEquiv.changeCoefficients_product γ (fun _ _ => rfl),
    KasparovDescentPairCoefficientEquiv.changeIntermediate_product]
  exact GradedKasparovHomotopyClass.regrade_product
    (reducedCrossedProductGrading_trivial α) rfl rfl _ _

/-- Actual intermediate pair transport of the coordinate-signed product used
by the already proved native odd-odd Morita reduction. -/
theorem evenGradedClass_product_coordinate_signed
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,max u (max uΓ (max uA (max uB uC)))} α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading)
    (y : GradedKasparovHomotopyClass.{uΓ,uB,uC,max u (max uΓ (max uA (max uB uC)))} (cliffordCoefficientAction β) γ
      cliffordCoefficientGrading CStarGrading.trivial) :
    evenGradedClass α γ (GroupUniverseProduct.product x y) =
      GroupUniverseProduct.product (coordinateGradedClass α β x) (signedGradedClass β γ y) := by
  unfold evenGradedClass coordinateGradedClass signedGradedClass
  rw [gradedClass_product.{uΓ,uA,uB,uC,u} α (cliffordCoefficientAction β) γ α.preservesGrading_trivial
    (cliffordCoefficientAction_preservesGrading β) γ.preservesGrading_trivial, KasparovDescentPairCoefficientEquiv.changeIntermediate_product]
  exact GradedKasparovHomotopyClass.regrade_product
    (reducedCrossedProductGrading_trivial α) rfl (reducedCrossedProductGrading_trivial γ) _ _

end BC4lean.KKTheory.KasparovDescent
