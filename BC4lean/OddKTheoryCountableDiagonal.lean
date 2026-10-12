import BC4lean.CountableModuleOperator
import BC4lean.FiniteModuleCompactMatrix
import BC4lean.OddKTheoryUnitaryFunctionalCalculus

/-! # Actual matrix coefficient actions on countable finite row modules

The proved countable module diagonal is bundled as a genuine unital star
algebra homomorphism. The actual forced-unitization matrix action on B^n is
also unital and then acts coordinatewise on the completed countable row sum.
Finite B-matrix entries between these rows are genuine compact operators.
No tensor-product identification or faithfulness of the unitization action
alone is asserted.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped CStarAlgebra

section Diagonal

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

theorem oddKTheoryCountableDiagonal_one :
    countableModuleDiagonal (1 : AdjointableMap B E E) =
      (1 : AdjointableMap B (CountableHilbertModuleSum B E) (CountableHilbertModuleSum B E)) := by
  ext x
  apply countableModule_ext_eval
  intro i
  simp only [countableModuleEvaluation_diagonal, AdjointableMap.one_apply]

theorem oddKTheoryCountableDiagonal_add (S T : AdjointableMap B E E) :
    countableModuleDiagonal (S + T) = countableModuleDiagonal S + countableModuleDiagonal T := by
  ext x
  apply countableModule_ext_eval
  intro i
  simp only [countableModuleEvaluation_diagonal, AdjointableMap.coe_add_apply, map_add]

theorem oddKTheoryCountableDiagonal_smul (c : ℂ) (S : AdjointableMap B E E) :
    countableModuleDiagonal (c • S) = c • countableModuleDiagonal S := by
  ext x
  apply countableModule_ext_eval
  intro i
  simp only [countableModuleEvaluation_diagonal, AdjointableMap.coe_smul_apply, map_smul]

theorem oddKTheoryCountableDiagonal_mul (S T : AdjointableMap B E E) :
    countableModuleDiagonal (S * T) = countableModuleDiagonal S * countableModuleDiagonal T := by
  ext x
  apply countableModule_ext_eval
  intro i
  simp only [countableModuleEvaluation_diagonal, AdjointableMap.mul_apply]

/-- The actual countable diagonal respects the complete unital star algebra
structure, by equality on genuine completed-module coordinate evaluations. -/
def oddKTheoryCountableDiagonalHom : AdjointableMap B E E →⋆ₐ[ℂ]
    AdjointableMap B (CountableHilbertModuleSum B E) (CountableHilbertModuleSum B E) where
  toFun := countableModuleDiagonal
  map_one' := oddKTheoryCountableDiagonal_one
  map_mul' := oddKTheoryCountableDiagonal_mul
  map_zero' := by
    ext x
    apply countableModule_ext_eval
    intro i
    simp only [countableModuleEvaluation_diagonal, AdjointableMap.coe_zero_apply, map_zero]
  map_add' := oddKTheoryCountableDiagonal_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, oddKTheoryCountableDiagonal_smul,
      oddKTheoryCountableDiagonal_one, Algebra.algebraMap_eq_smul_one]
  map_star' S := countableModuleDiagonal_adjoint S

theorem continuous_oddKTheoryCountableDiagonalHom :
    Continuous (oddKTheoryCountableDiagonalHom (B := B) (E := E)) :=
  map_continuous (oddKTheoryCountableDiagonalHom (B := B) (E := E))

end Diagonal

section FiniteRows

variable {B ι : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [DecidableEq ι]

/-- The matrix identity acts as the actual row-module identity, including
empty finite coordinate types and zero coefficient algebras. -/
theorem oddKTheoryUnitizedRowMatrix_one :
    unitizedModuleMatrixRepresentation (1 : CStarMatrix ι ι (Unitization ℂ B)) =
      (1 : AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι)) := by
  ext x i
  simp only [unitizedModuleMatrixRepresentation_apply, CStarMatrix.one_apply,
    AdjointableMap.one_apply]
  calc
    (∑ j : ι, unitizedStandardLeftMul (B := B) (if i = j then 1 else 0) (x j)) =
        ∑ j : ι, if i = j then x j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j
      · simp only [if_pos hij, map_one, AdjointableMap.one_apply]
      · simp only [if_neg hij, map_zero, AdjointableMap.coe_zero_apply]
    _ = x i := Fintype.sum_ite_eq i (fun j : ι => x j)

/-- The genuine full matrix action on B^n, with its unital structure retained. -/
def oddKTheoryUnitizedRowMatrixHom : CStarMatrix ι ι (Unitization ℂ B) →⋆ₐ[ℂ]
    AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι) where
  toFun := unitizedModuleMatrixRepresentation
  map_one' := oddKTheoryUnitizedRowMatrix_one
  map_mul' := map_mul unitizedModuleMatrixRepresentation
  map_zero' := map_zero unitizedModuleMatrixRepresentation
  map_add' := map_add unitizedModuleMatrixRepresentation
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, oddKTheoryUnitizedRowMatrix_one,
      Algebra.algebraMap_eq_smul_one]
  map_star' := map_star unitizedModuleMatrixRepresentation

/-- Actual matrix coefficients acting coordinatewise on the genuine countable
sum of finite row modules, with no tensor identification involved. -/
def oddKTheoryCountableRowMatrixHom : CStarMatrix ι ι (Unitization ℂ B) →⋆ₐ[ℂ]
    AdjointableMap B (CountableHilbertModuleSum B (FiniteStandardModule B ι))
      (CountableHilbertModuleSum B (FiniteStandardModule B ι)) :=
  oddKTheoryCountableDiagonalHom.comp oddKTheoryUnitizedRowMatrixHom

@[simp] theorem oddKTheoryCountableRowMatrixHom_evaluation
    (M : CStarMatrix ι ι (Unitization ℂ B)) (n : ℕ)
    (x : CountableHilbertModuleSum B (FiniteStandardModule B ι)) :
    countableModuleEvaluation (B := B) n (oddKTheoryCountableRowMatrixHom M x) =
      unitizedModuleMatrixRepresentation M (countableModuleEvaluation (B := B) n x) :=
  countableModuleEvaluation_diagonal _ _ _

/-- A genuine B-matrix coefficient between two actual countable row
coordinates is compact for possibly nonunital B. -/
def oddKTheoryCountableRowCoefficient (n m : ℕ) (M : CStarMatrix ι ι B) :
    AdjointableMap B (CountableHilbertModuleSum B (FiniteStandardModule B ι))
      (CountableHilbertModuleSum B (FiniteStandardModule B ι)) :=
  ((countableModuleInclusion (B := B) n).comp (moduleMatrixRepresentation M)).comp
    (countableModuleEvaluation (B := B) m)

theorem oddKTheoryCountableRowCoefficient_isModuleCompact
    (n m : ℕ) (M : CStarMatrix ι ι B) :
    IsModuleCompact (oddKTheoryCountableRowCoefficient n m M) :=
  ((moduleMatrixRepresentation_isModuleCompact M).comp_left
    (countableModuleInclusion (B := B) n)).comp_right (countableModuleEvaluation (B := B) m)

local instance oddContinuationOddKTheoryCountableDiagonalLocalInstance01 :
    PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
local instance oddContinuationOddKTheoryCountableDiagonalLocalInstance02 :
    StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ

omit [PartialOrder B] [StarOrderedRing B] in
/-- The full finite scalar matrix quotient commutes with actual circle CFC.
At a scalar-identity input its value is the scalar base-point value times I. -/
theorem oddKTheoryRowCircleCFC_scalar_matrix
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1)
    (f : C(Circle, ℂ)) :
    unitizationScalarMatrix (oddKTheoryCircleCFC u f) =
      algebraMap ℂ (CStarMatrix ι ι ℂ) (f 1) := by
  let φ := OperatorKTheory.matrixMap (ι := ι) (OperatorKTheory.scalarQuotient B)
  have hφ : Continuous φ :=
    AddMonoidHomClass.continuous_of_bound φ 1 (fun M => by
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le φ M)
  have hu' : φ (u : CStarMatrix ι ι (Unitization ℂ B)) =
      (1 : unitary (CStarMatrix ι ι ℂ)) := hu
  have h := oddKTheoryCircleCFC_map φ hφ u (1 : unitary (CStarMatrix ι ι ℂ)) hu' f
  exact h.trans (oddKTheoryCircleCFC_one_algebraMap f)

/-- Extract the actual B-matrix entries of a circle coefficient, preserving
the full forced-unitization scalar quotient separately. -/
def oddKTheoryRowCircleCFCCoefficientMatrix
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) (f : C(Circle, ℂ)) :
    CStarMatrix ι ι B := (oddKTheoryCircleCFC u f).map fun a => a.snd

omit [PartialOrder B] [StarOrderedRing B] in
theorem oddKTheoryRowCircleCFC_eq_coefficientMatrix
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1)
    (f : C(Circle, ℂ)) (hf : f 1 = 0) :
    oddKTheoryCircleCFC u f =
      unitizationCoefficientMatrix (oddKTheoryRowCircleCFCCoefficientMatrix u f) := by
  have hscalar : unitizationScalarMatrix (oddKTheoryCircleCFC u f) = 0 := by
    rw [oddKTheoryRowCircleCFC_scalar_matrix u hu f, hf, map_zero]
  apply CStarMatrix.ext
  intro i j
  apply Unitization.ext
  · have h := congrArg (fun M : CStarMatrix ι ι ℂ => M i j) hscalar
    simpa only [unitizationScalarMatrix_apply, CStarMatrix.zero_apply,
      unitizationCoefficientMatrix_apply, Unitization.fst_inr] using h
  · rfl

/-- An actual circle coefficient vanishing at 1 becomes a compact finite
row-module operator after evaluation at a full scalar-identity matrix unitary. -/
theorem oddKTheoryRowCircleCFC_isModuleCompact
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1)
    (f : C(Circle, ℂ)) (hf : f 1 = 0) :
    IsModuleCompact (unitizedModuleMatrixRepresentation (oddKTheoryCircleCFC u f)) := by
  rw [oddKTheoryRowCircleCFC_eq_coefficientMatrix u hu f hf,
    unitizedModuleMatrixRepresentation_coefficient]
  exact moduleMatrixRepresentation_isModuleCompact _

/-- The compactness survives placing the coefficient between any two actual
rows in the genuine countable completed finite-row module. -/
theorem oddKTheoryCountableRowCircleCFCEntry_isModuleCompact
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1)
    (f : C(Circle, ℂ)) (hf : f 1 = 0) (n m : ℕ) :
    IsModuleCompact (((countableModuleInclusion (B := B) n).comp
      (unitizedModuleMatrixRepresentation (oddKTheoryCircleCFC u f))).comp
        (countableModuleEvaluation (B := B) m)) :=
  ((oddKTheoryRowCircleCFC_isModuleCompact u hu f hf).comp_left
    (countableModuleInclusion (B := B) n)).comp_right (countableModuleEvaluation (B := B) m)

end FiniteRows
end BC4lean.KKTheory
