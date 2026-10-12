import BC4lean.GroupUniverseCompactCorrespondenceProduct
import BC4lean.GroupUniverseMatrixMoritaBridge

/-! # Independent-universe matrix Morita maps are actual products

The row and column modules give genuine zero-operator correspondence
classes. The full matrix Morita quotient maps equal their actual class
products. Consequently true graded product associativity proves their
compatibility with every preceding genuine product.
-/

noncomputable section
universe uΓ uA uB uC uE uF
namespace BC4lean.KKTheory.GroupUniverseMatrixMoritaProduct
open GradedMatrixMoritaEquivariant

variable {Γ : Type uΓ} {C : Type uC} [Group Γ]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace C] (γ : CStarAlgebraAction Γ C)

def columnClass : GradedKasparovHomotopyClass.{uΓ,uC,uC,uC}
    (matrixAction γ) γ GradedMatrixMoritaMatrix.grading CStarGrading.trivial :=
  GroupUniverseCompactCorrespondenceProduct.correspondenceClass
    (matrixAction γ) γ GradedMatrixMoritaMatrix.grading CStarGrading.trivial
    GradedMatrixMoritaColumn.grading (columnAction γ)
    (matrixAction_preservesGrading γ) γ.preservesGrading_trivial
    (columnAction_preservesGrading γ) GradedMatrixMoritaColumn.leftAction
    GradedMatrixMoritaColumn.leftAction_graded (columnRepresentation_equivariant γ)
    GradedMatrixMoritaColumn.leftAction_compact GradedMatrixMoritaColumn.countablyGenerated

def rowClass : GradedKasparovHomotopyClass.{uΓ,uC,uC,uC}
    γ (matrixAction γ) CStarGrading.trivial GradedMatrixMoritaMatrix.grading :=
  GroupUniverseCompactCorrespondenceProduct.correspondenceClass
    γ (matrixAction γ) CStarGrading.trivial GradedMatrixMoritaMatrix.grading
    GradedMatrixMoritaRow.grading (rowAction γ)
    γ.preservesGrading_trivial (matrixAction_preservesGrading γ)
    (rowAction_preservesGrading γ) GradedMatrixMoritaRow.leftAction
    GradedMatrixMoritaRow.leftAction_graded (rowRepresentation_equivariant γ)
    GradedMatrixMoritaRow.leftAction_compact GradedMatrixMoritaRow.countablyGenerated

variable {A : Type uA} [NonUnitalCStarAlgebra A]
  [TopologicalSpace.SeparableSpace A] [Countable Γ]
  {α : CStarAlgebraAction Γ A} {δA : CStarGrading A}

theorem toCoefficientClass_eq_product
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uC,uE} α (matrixAction γ)
      δA GradedMatrixMoritaMatrix.grading) :
    GroupUniverseMatrixMoritaBridge.toCoefficientClass x =
      GroupUniverseProduct.product x (columnClass γ) := by
  refine Quotient.inductionOn x ?_
  intro c
  exact GroupUniverseCompactCorrespondenceProduct.tensorClass_eq_product
    (matrixAction γ) γ GradedMatrixMoritaMatrix.grading CStarGrading.trivial
    GradedMatrixMoritaColumn.grading (columnAction γ)
    (matrixAction_preservesGrading γ) γ.preservesGrading_trivial
    (columnAction_preservesGrading γ) GradedMatrixMoritaColumn.leftAction
    GradedMatrixMoritaColumn.leftAction_graded (columnRepresentation_equivariant γ)
    GradedMatrixMoritaColumn.leftAction_compact GradedMatrixMoritaColumn.countablyGenerated
    c.cycle

theorem toMatrixClass_eq_product
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uC,uE} α γ δA CStarGrading.trivial) :
    GroupUniverseMatrixMoritaBridge.toMatrixClass x =
      GroupUniverseProduct.product x (rowClass γ) := by
  refine Quotient.inductionOn x ?_
  intro c
  exact GroupUniverseCompactCorrespondenceProduct.tensorClass_eq_product
    γ (matrixAction γ) CStarGrading.trivial GradedMatrixMoritaMatrix.grading
    GradedMatrixMoritaRow.grading (rowAction γ)
    γ.preservesGrading_trivial (matrixAction_preservesGrading γ)
    (rowAction_preservesGrading γ) GradedMatrixMoritaRow.leftAction
    GradedMatrixMoritaRow.leftAction_graded (rowRepresentation_equivariant γ)
    GradedMatrixMoritaRow.leftAction_compact GradedMatrixMoritaRow.countablyGenerated
    c.cycle

variable {B : Type uB} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B] {β : CStarAlgebraAction Γ B} {δB : CStarGrading B}

/-- The true column map commutes with an arbitrary preceding product;
both sides have module universe `max uE uF uC`. -/
theorem toCoefficientClass_product
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β δA δB)
    (y : GradedKasparovHomotopyClass.{uΓ,uB,uC,uF} β (matrixAction γ)
      δB GradedMatrixMoritaMatrix.grading) :
    GroupUniverseMatrixMoritaBridge.toCoefficientClass (GroupUniverseProduct.product x y) =
      GroupUniverseProduct.product x (GroupUniverseMatrixMoritaBridge.toCoefficientClass y) := by
  rw [toCoefficientClass_eq_product, toCoefficientClass_eq_product]
  exact GroupUniverseProduct.product_assoc x y (columnClass γ)

/-- The same genuine product compatibility holds for the row map. -/
theorem toMatrixClass_product
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β δA δB)
    (y : GradedKasparovHomotopyClass.{uΓ,uB,uC,uF} β γ δB CStarGrading.trivial) :
    GroupUniverseMatrixMoritaBridge.toMatrixClass (GroupUniverseProduct.product x y) =
      GroupUniverseProduct.product x (GroupUniverseMatrixMoritaBridge.toMatrixClass y) := by
  rw [toMatrixClass_eq_product, toMatrixClass_eq_product]
  exact GroupUniverseProduct.product_assoc x y (rowClass γ)

end BC4lean.KKTheory.GroupUniverseMatrixMoritaProduct
