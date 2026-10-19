import BC4lean.ReducedCrossedHilbertGrading
import BC4lean.ReducedCrossedProduct
import BC4lean.GradingConjugateOperator

/-! # The coefficient grading acts on the actual regular representation

Coordinatewise coefficient grading is semilinear over the coefficient algebra.
Its genuine conjugation on adjointable operators sends π(b) to π(β(b)) and
fixes translations when the group action preserves β. These are equalities
of the actual completed-module operators defining the reduced crossed product.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ B : Type*} [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder B] [StarOrderedRing B] in
/-- Coordinate grading conjugates a diagonal family by the coefficient grading. -/
theorem reducedCrossedFiniteGrading_diagonal (β : CStarGrading B) (a : Γ → B)
    (x : ReducedCrossedVectors B Γ) :
    reducedCrossedFiniteGradingLinear β
      (reducedCrossedFiniteDiagonal a (reducedCrossedFiniteGradingLinear β x)) =
      reducedCrossedFiniteDiagonal (fun i => β.automorphism (a i)) x := by
  ext i
  simp only [reducedCrossedFiniteGradingLinear_apply, reducedCrossedFiniteDiagonal_apply,
    opStarAlgEquiv_apply, MulOpposite.unop_op, map_mul,
    CStarGrading.automorphism_sq]

omit [PartialOrder B] [StarOrderedRing B] in
/-- Coordinate grading commutes with every coordinate permutation. -/
theorem reducedCrossedFiniteGrading_reindex (β : CStarGrading B) (e : Γ ≃ Γ)
    (x : ReducedCrossedVectors B Γ) :
    reducedCrossedFiniteGradingLinear β
        (reducedCrossedEmbeddingLinear e.toEmbedding
          (reducedCrossedFiniteGradingLinear β x)) =
      reducedCrossedEmbeddingLinear e.toEmbedding x := by
  ext i
  simp only [reducedCrossedFiniteGradingLinear_apply,
    reducedCrossedEmbeddingLinear_equiv_apply, CStarGrading.op_automorphism_sq]

variable [Group Γ]

/-- Actual grading conjugation transforms the twisted coefficient operator. -/
@[simp] theorem reducedCrossedGrading_coefficient (α : CStarAlgebraAction Γ B)
    (β : CStarGrading B) (hα : α.PreservesGrading β) (b : B) :
    (reducedCrossedHilbertGrading (Γ := Γ) β).conjugateOperatorStarAlgEquiv
        (reducedCrossedCoefficient α b) =
      reducedCrossedCoefficient α (β.automorphism b) := by
  apply reducedCrossedRegular_ext
  intro x
  simp only [GradedHilbertModule.conjugateOperatorStarAlgEquiv_apply,
    GradedHilbertModule.conjugateOperator_apply, reducedCrossedHilbertGrading_mk,
    reducedCrossedCoefficient_mk]
  rw [reducedCrossedFiniteGrading_diagonal]
  congr 1
  exact congrArg (fun a : Γ → B => reducedCrossedFiniteDiagonal a x)
    (funext fun i => (hα i⁻¹ b).symm)

/-- Actual grading conjugation fixes the genuine translation unitary. -/
@[simp] theorem reducedCrossedGrading_regular (β : CStarGrading B) (g : Γ) :
    (reducedCrossedHilbertGrading (Γ := Γ) β).conjugateOperatorStarAlgEquiv
        (reducedCrossedRegular (B := B) g) = reducedCrossedRegular g := by
  apply reducedCrossedRegular_ext
  intro x
  simp only [GradedHilbertModule.conjugateOperatorStarAlgEquiv_apply,
    GradedHilbertModule.conjugateOperator_apply, reducedCrossedHilbertGrading_mk,
    reducedCrossedRegular_mk]
  rw [reducedCrossedFiniteGrading_reindex]

/-- The induced grading has the required formula on each crossed-product generator. -/
@[simp] theorem reducedCrossedGrading_generator (α : CStarAlgebraAction Γ B)
    (β : CStarGrading B) (hα : α.PreservesGrading β) (b : B) (g : Γ) :
    (reducedCrossedHilbertGrading (Γ := Γ) β).conjugateOperatorStarAlgEquiv
        (reducedCrossedGenerator α b g) =
      reducedCrossedGenerator α (β.automorphism b) g := by
  simp only [reducedCrossedGenerator, map_mul,
    reducedCrossedGrading_coefficient α β hα, reducedCrossedGrading_regular]

end BC4lean.KKTheory
