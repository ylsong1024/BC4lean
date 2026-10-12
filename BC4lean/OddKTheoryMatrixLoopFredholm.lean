import BC4lean.OddKTheoryLoopSquareTransfer

/-! # Actual compact square defect of the matrix-unitary pullback

An actual finite matrix unitary with full scalar matrix quotient I produces
a genuine selfadjoint bounded operator on the completed countable sum of
B-valued finite rows. Its square defect consists of four actual B-matrix
entries and is consequently module compact, including for nonunital B.
This supplies a genuine infinite-module Fredholm operator; the odd KK/K1
comparison and its inverse-composition homotopies are not asserted here.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B ι : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [DecidableEq ι]

/-- Actual circle coefficient action on a single finite B-valued row. -/
def oddKTheoryMatrixRowCircleAction
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) :
    C(Circle, ℂ) →⋆ₐ[ℂ] AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι) :=
  oddKTheoryUnitizedRowMatrixHom.comp (oddKTheoryCircleCFC u)

/-- The actual twenty-one-term formula is the previously defined bounded
matrix-unitary pullback operator. -/
theorem oddKTheoryMatrixLoopPullback_finiteFormula
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) :
    oddKTheoryMatrixLoopPullback u =
      oddKTheoryFiniteRowFormula (oddKTheoryMatrixRowCircleAction u)
        oddKTheoryLoopTermCoefficient oddKTheoryRowLoopTermOperator := by
  unfold oddKTheoryFiniteRowFormula
  simp only [Fintype.sum_sum_type, oddKTheoryLoopTermCoefficient,
    oddKTheoryRowLoopTermOperator, Fintype.sum_unique]
  change _ + _ + _ = _ + (_ + _)
  exact add_assoc _ _ _

/-- The actual infinite-module square defect is exactly the four periodic
finite coefficient entries, proved by scalar entry transfer. -/
theorem oddKTheoryMatrixLoopPullback_square_defect
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) :
    oddKTheoryMatrixLoopPullback u * oddKTheoryMatrixLoopPullback u - 1 =
      ∑ i : Fin 4, oddKTheoryMatrixCircleCoefficient u (oddKTheoryLoopDefectCircleEntry i) *
        oddKTheoryRowLoopFixedFiniteOperator i := by
  rw [oddKTheoryMatrixLoopPullback_finiteFormula,
    oddKTheoryFiniteRowFormula_loop_square]
  change 1 + _ - 1 = _
  abel

/-- A base-point-zero coefficient in any of the four finite correction
positions is a genuine compact B-matrix row entry. -/
theorem oddKTheoryMatrixCircleFiniteEntry_isModuleCompact
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1)
    (f : C(Circle, ℂ)) (hf : f 1 = 0) (i : Fin 4) :
    IsModuleCompact (oddKTheoryMatrixCircleCoefficient u f *
      oddKTheoryRowLoopFixedFiniteOperator i) := by
  rw [oddKTheoryRowLoopFixedFiniteOperator_matrixUnit]
  change IsModuleCompact (countableModuleDiagonal
    (unitizedModuleMatrixRepresentation (oddKTheoryCircleCFC u f)) * _)
  rw [oddKTheoryRowDiagonal_mul_integerMatrixUnit]
  exact ((oddKTheoryRowCircleCFC_isModuleCompact u hu f hf).comp_left
    (oddKTheoryRowIntegerInclusion _)).comp_right (oddKTheoryRowIntegerInclusion _).adjoint

/-- The genuine compact square condition, using the full scalar matrix
quotient and four B-valued entries rather than compact coordinate identities. -/
theorem oddKTheoryMatrixLoopPullback_square_isModuleCompact
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    IsModuleCompact (oddKTheoryMatrixLoopPullback u * oddKTheoryMatrixLoopPullback u - 1) := by
  rw [oddKTheoryMatrixLoopPullback_square_defect]
  exact (moduleCompact B (CountableHilbertModuleSum B (FiniteStandardModule B ι))
    (CountableHilbertModuleSum B (FiniteStandardModule B ι))).sum_mem
      (fun i _ => oddKTheoryMatrixCircleFiniteEntry_isModuleCompact u hu _
        (oddKTheoryLoopDefectCircleEntry_one i) i)

/-- All operator conditions supplied by the unitary-to-infinite-Fredholm
construction, stated without claiming either comparison composition. -/
theorem oddKTheoryMatrixLoopPullback_fredholm_conditions
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    IsSelfAdjoint (oddKTheoryMatrixLoopPullback u) ∧
      IsModuleCompact (oddKTheoryMatrixLoopPullback u * oddKTheoryMatrixLoopPullback u - 1) :=
  ⟨oddKTheoryMatrixLoopPullback_isSelfAdjoint u,
    oddKTheoryMatrixLoopPullback_square_isModuleCompact u hu⟩

end BC4lean.KKTheory
