import BC4lean.ReducedCrossedProductGrading
import BC4lean.KasparovDescentModule
import BC4lean.GradedEquivariantInteriorModuleTensor
import BC4lean.StandardHilbertModuleActions

/-! # Genuine grading on the actual reduced-descent coefficient module

The coefficient embedding intertwines the original grading with the proved
grading on the concrete reduced crossed product. This gives the actual
balanced grading on `E ⊗_B (B ⋊ᵣ Γ)` and proves that the actual tensor operator
`F ⊗ 1` retains its parity. No crossed-product source representation or
Kasparov descent map is asserted by these module constructions.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent

open scoped KasparovDescent

variable {Γ B : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]

/-- The actual crossed coefficient algebra, regarded as its standard graded module. -/
def crossedStandardGrading (α : CStarAlgebraAction Γ B) (δB : CStarGrading B)
    (hα : α.PreservesGrading δB) :
    GradedHilbertModule (reducedCrossedProductGrading α δB hα)
      (ReducedCrossedProduct α)ᵐᵒᵖ :=
  GradedHilbertModule.standard (reducedCrossedProductGrading α δB hα)

/-- The genuine coefficient representation respects the original and crossed gradings. -/
theorem coefficientRepresentation_graded (α : CStarAlgebraAction Γ B)
    (δB : CStarGrading B) (hα : α.PreservesGrading δB) :
    ModuleTensorRepresentationGraded (δB := δB) (coefficientRepresentation α)
      (crossedStandardGrading α δB hα) := by
  intro b c
  change MulOpposite.op ((reducedCrossedProductGrading α δB hα).automorphism
      (coefficientToReducedCrossed α b * MulOpposite.unop c)) =
    MulOpposite.op (coefficientToReducedCrossed α (δB.automorphism b) *
      (reducedCrossedProductGrading α δB hα).automorphism (MulOpposite.unop c))
  rw [map_mul, reducedCrossedProductGrading_coefficient]

/-- Grading conjugation has the expected formula on actual coefficient operators. -/
@[simp] theorem coefficientRepresentation_grading_conjugate
    (α : CStarAlgebraAction Γ B) (δB : CStarGrading B)
    (hα : α.PreservesGrading δB) (b : B) :
    (crossedStandardGrading α δB hα).conjugateOperatorStarAlgEquiv
        (coefficientRepresentation α b) =
      coefficientRepresentation α (δB.automorphism b) := by
  ext c
  change (crossedStandardGrading α δB hα).grading
      (coefficientRepresentation α b ((crossedStandardGrading α δB hα).grading c)) =
    coefficientRepresentation α (δB.automorphism b) c
  rw [coefficientRepresentation_graded α δB hα b,
    GradedHilbertModule.grading_sq]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- The actual completed interior module carries its induced semilinear grading. -/
def moduleGrading (α : CStarAlgebraAction Γ B) (δB : CStarGrading B)
    (hα : α.PreservesGrading δB) (J : GradedHilbertModule δB E) :
    GradedHilbertModule (reducedCrossedProductGrading α δB hα) (Module α E) :=
  J.interiorTensor (crossedStandardGrading α δB hα)
    (coefficientRepresentation_graded α δB hα)

/-- The completed grading acts by the original and coefficient gradings on elementary tensors. -/
@[simp] theorem moduleGrading_mk (α : CStarAlgebraAction Γ B) (δB : CStarGrading B)
    (hα : α.PreservesGrading δB) (J : GradedHilbertModule δB E) (x : E)
    (c : (ReducedCrossedProduct α)ᵐᵒᵖ) :
    (moduleGrading α δB hα J).grading (mk α E x c) =
      mk α E (J.grading x)
        (MulOpposite.op ((reducedCrossedProductGrading α δB hα).automorphism
          (MulOpposite.unop c))) :=
  GradedHilbertModule.interiorTensor_grading_mk J (crossedStandardGrading α δB hα)
    (coefficientRepresentation_graded α δB hα) x c

/-- A genuinely odd original operator gives a genuinely odd completed tensor operator. -/
theorem operatorHom_odd (α : CStarAlgebraAction Γ B) (δB : CStarGrading B)
    (hα : α.PreservesGrading δB) (J : GradedHilbertModule δB E)
    {F : AdjointableMap B E E} (hF : J.IsOdd J F) :
    (moduleGrading α δB hα J).IsOdd (moduleGrading α δB hα J)
      (operatorHom α E F) :=
  hF.interiorModuleTensorOperator (crossedStandardGrading α δB hα)
    (coefficientRepresentation_graded α δB hα)

/-- Evenness is also retained by the actual tensor operator homomorphism. -/
theorem operatorHom_even (α : CStarAlgebraAction Γ B) (δB : CStarGrading B)
    (hα : α.PreservesGrading δB) (J : GradedHilbertModule δB E)
    {F : AdjointableMap B E E} (hF : J.IsEven J F) :
    (moduleGrading α δB hα J).IsEven (moduleGrading α δB hα J)
      (operatorHom α E F) :=
  hF.interiorModuleTensorOperator (crossedStandardGrading α δB hα)
    (coefficientRepresentation_graded α δB hα)

end BC4lean.KKTheory.KasparovDescent
