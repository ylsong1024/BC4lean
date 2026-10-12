import BC4lean.OddKTheoryRowPeriodicExpansion

/-! # Actual bounded pullback of the periodic row-module formula

Every matrix unitary supplies actual circle CFC coefficients, acting
coordinatewise on the genuine countable finite-row module. The finite
periodic formula therefore defines a bounded adjointable operator and varies
continuously with the matrix unitary. Its identity value is the actual sign
symmetry, and its four finite correction terms are genuinely compact for
full scalar-identity coefficient unitaries.

The square-defect identity for this evaluated infinite operator, exponential
class recovery, and the arbitrary-cycle inverse-composition homotopy are
further obligations; this module does not assert the odd comparison.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped CStarAlgebra

variable {B ι : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [DecidableEq ι]

abbrev OddKTheoryMatrixRowOperator (B ι : Type*) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] [Fintype ι] [DecidableEq ι] :=
  OddKTheoryCountableOperator B (FiniteStandardModule B ι)

/-- Actual CFC matrix coefficients acting on each genuine completed row. -/
def oddKTheoryMatrixCircleCoefficient
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) (f : C(Circle, ℂ)) :
    OddKTheoryMatrixRowOperator B ι :=
  oddKTheoryCountableRowMatrixHom (oddKTheoryCircleCFC u f)

theorem continuous_oddKTheoryMatrixCircleCoefficient (f : C(Circle, ℂ)) :
    Continuous (fun u : unitary (CStarMatrix ι ι (Unitization ℂ B)) =>
      oddKTheoryMatrixCircleCoefficient u f) :=
  (map_continuous (oddKTheoryCountableRowMatrixHom (B := B) (ι := ι))).comp (continuous_oddKTheoryCircleCFC_unitary f)

/-- The actual bounded infinite-row operator defined by the finite periodic
circle-coefficient formula. -/
def oddKTheoryMatrixLoopPullback
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) : OddKTheoryMatrixRowOperator B ι :=
  (∑ p : Fin 4 × Fin 4,
      oddKTheoryMatrixCircleCoefficient u (oddKTheoryLoopResidualCircleCoefficient p) *
        oddKTheoryRowLoopFixedOperator p) +
    oddKTheoryMatrixCircleCoefficient u oddKTheoryLoopSignCircleCoefficient *
      oddKTheoryRowSignOperator +
    ∑ i : Fin 4,
      oddKTheoryMatrixCircleCoefficient u (oddKTheoryLoopFiniteCircleCoefficient i) *
        oddKTheoryRowLoopFixedFiniteOperator i

theorem continuous_oddKTheoryMatrixLoopPullback :
    Continuous (oddKTheoryMatrixLoopPullback (B := B) (ι := ι)) := by
  have hc := continuous_oddKTheoryMatrixCircleCoefficient (B := B) (ι := ι)
  unfold oddKTheoryMatrixLoopPullback
  fun_prop

/-- The matrix identity pulls back to the actual degenerate sign symmetry. -/
@[simp] theorem oddKTheoryMatrixLoopPullback_one :
    oddKTheoryMatrixLoopPullback (1 : unitary (CStarMatrix ι ι (Unitization ℂ B))) =
      oddKTheoryRowSignOperator := by
  simp only [oddKTheoryMatrixLoopPullback, oddKTheoryMatrixCircleCoefficient,
    oddKTheoryCircleCFC_one_algebraMap, oddKTheoryLoopResidualCircleCoefficient_one,
    oddKTheoryLoopSignCircleCoefficient_one, oddKTheoryLoopFiniteCircleCoefficient_one,
    map_zero, map_one, zero_mul, one_mul, Finset.sum_const_zero, zero_add, add_zero]

/-- Actual row-coordinate matrix units without a B-valued identity
coefficient. They are not declared compact. -/
def oddKTheoryRowIntegerMatrixUnit (z w : ℤ) :
    OddKTheoryCountableOperator B (FiniteStandardModule B ι) :=
  (oddKTheoryRowIntegerInclusion z).comp (oddKTheoryRowIntegerInclusion w).adjoint

omit [DecidableEq ι] in
theorem oddKTheoryRowIntegerMatrixUnit_inclusion [DecidableEq ι] (z w k : ℤ)
    (b : FiniteStandardModule B ι) :
    oddKTheoryRowIntegerMatrixUnit z w (oddKTheoryRowIntegerInclusion k b) =
      if k = w then oddKTheoryRowIntegerInclusion z b else 0 := by
  change countableModuleInclusion (B := B) (E := FiniteStandardModule B ι)
      (oddKTheoryRowIntegerIndex z)
      (countableModuleEvaluation (B := B) (E := FiniteStandardModule B ι)
        (oddKTheoryRowIntegerIndex w)
        (countableModuleInclusion (B := B) (E := FiniteStandardModule B ι)
          (oddKTheoryRowIntegerIndex k) b)) =
    if k = w then countableModuleInclusion (B := B) (E := FiniteStandardModule B ι)
      (oddKTheoryRowIntegerIndex z) b else 0
  rw [countableModuleEvaluation_inclusion]
  by_cases h : k = w
  · subst k
    simp only [if_true]
  · have hn : oddKTheoryRowIntegerIndex k ≠ oddKTheoryRowIntegerIndex w :=
      fun he => h (Equiv.intEquivNat.injective he)
    simp only [if_neg hn, if_neg h, map_zero]

/-- The four actual finite correction operators are precisely these
zero/minus-one row-coordinate matrix units. -/
theorem oddKTheoryRowLoopFixedFiniteOperator_matrixUnit (i : Fin 4) :
    oddKTheoryRowLoopFixedFiniteOperator (B := B) (E := FiniteStandardModule B ι) i =
      oddKTheoryRowIntegerMatrixUnit (![0, 0, -1, -1] i) (![0, -1, 0, -1] i) := by
  fin_cases i
  · change oddKTheoryRowZeroProjection (B := B) (E := FiniteStandardModule B ι) =
      oddKTheoryRowIntegerMatrixUnit (B := B) (ι := ι) 0 0
    apply oddKTheoryRowOperator_ext_integerCoordinates
    intro z b
    rw [oddKTheoryRowZeroProjection_inclusion, oddKTheoryRowIntegerMatrixUnit_inclusion]
    by_cases hz : z = 0
    · subst z
      simp only [if_true]
    · simp only [if_neg hz]
  · change oddKTheoryRowZeroProjection (B := B) (E := FiniteStandardModule B ι) *
      oddKTheoryRowReflectionOperator (-1) = oddKTheoryRowIntegerMatrixUnit (B := B) (ι := ι) 0 (-1)
    apply oddKTheoryRowOperator_ext_integerCoordinates
    intro z b
    rw [AdjointableMap.mul_apply, oddKTheoryRowReflectionOperator_inclusion,
      oddKTheoryRowZeroProjection_inclusion, oddKTheoryRowIntegerMatrixUnit_inclusion]
    by_cases hz : z = -1
    · subst z
      norm_num
    · have hn : -z + (-1) ≠ 0 := by omega
      simp only [if_neg hn, if_neg hz]
  · change oddKTheoryRowReflectionOperator (B := B) (E := FiniteStandardModule B ι) (-1) *
      oddKTheoryRowZeroProjection = oddKTheoryRowIntegerMatrixUnit (B := B) (ι := ι) (-1) 0
    apply oddKTheoryRowOperator_ext_integerCoordinates
    intro z b
    rw [AdjointableMap.mul_apply, oddKTheoryRowZeroProjection_inclusion,
      oddKTheoryRowIntegerMatrixUnit_inclusion]
    by_cases hz : z = 0
    · subst z
      simp only [if_true, oddKTheoryRowReflectionOperator_inclusion, neg_zero, zero_add]
    · simp only [if_neg hz, map_zero]
  · change oddKTheoryRowReflectionOperator (B := B) (E := FiniteStandardModule B ι) (-1) *
      oddKTheoryRowZeroProjection * oddKTheoryRowReflectionOperator (-1) =
      oddKTheoryRowIntegerMatrixUnit (B := B) (ι := ι) (-1) (-1)
    apply oddKTheoryRowOperator_ext_integerCoordinates
    intro z b
    rw [AdjointableMap.mul_apply, AdjointableMap.mul_apply,
      oddKTheoryRowReflectionOperator_inclusion, oddKTheoryRowZeroProjection_inclusion,
      oddKTheoryRowIntegerMatrixUnit_inclusion]
    by_cases hz : z = -1
    · subst z
      norm_num
    · have hn : -z + (-1) ≠ 0 := by omega
      simp only [if_neg hn, if_neg hz, map_zero]

omit [DecidableEq ι] in
/-- Genuine diagonal coefficient action times a row matrix unit is exactly
the actual finite row coefficient entry. -/
theorem oddKTheoryRowDiagonal_mul_integerMatrixUnit
    [DecidableEq ι] (S : AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι)) (z w : ℤ) :
    countableModuleDiagonal S * oddKTheoryRowIntegerMatrixUnit z w =
      ((oddKTheoryRowIntegerInclusion z).comp S).comp (oddKTheoryRowIntegerInclusion w).adjoint := by
  ext x
  simp only [AdjointableMap.mul_apply, oddKTheoryRowIntegerMatrixUnit,
    AdjointableMap.comp_apply, oddKTheoryRowDiagonal_integerInclusion]

/-- Each finite periodic term becomes a genuine compact row coefficient
entry under the full scalar matrix identity condition. -/
theorem oddKTheoryMatrixLoopPullback_finiteTerm_isModuleCompact
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) (i : Fin 4) :
    IsModuleCompact (oddKTheoryMatrixCircleCoefficient u (oddKTheoryLoopFiniteCircleCoefficient i) *
      oddKTheoryRowLoopFixedFiniteOperator i) := by
  rw [oddKTheoryRowLoopFixedFiniteOperator_matrixUnit]
  change IsModuleCompact (countableModuleDiagonal
    (unitizedModuleMatrixRepresentation (oddKTheoryCircleCFC u (oddKTheoryLoopFiniteCircleCoefficient i))) * _)
  rw [oddKTheoryRowDiagonal_mul_integerMatrixUnit]
  exact ((oddKTheoryRowCircleCFC_isModuleCompact u hu _
    (oddKTheoryLoopFiniteCircleCoefficient_one i)).comp_left
      (oddKTheoryRowIntegerInclusion _)).comp_right (oddKTheoryRowIntegerInclusion _).adjoint

theorem oddKTheoryMatrixLoopPullback_finiteCorrection_isModuleCompact
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    IsModuleCompact (∑ i : Fin 4,
      oddKTheoryMatrixCircleCoefficient u (oddKTheoryLoopFiniteCircleCoefficient i) *
        oddKTheoryRowLoopFixedFiniteOperator i) :=
  (moduleCompact B (CountableHilbertModuleSum B (FiniteStandardModule B ι))
    (CountableHilbertModuleSum B (FiniteStandardModule B ι))).sum_mem
      (fun i _ => oddKTheoryMatrixLoopPullback_finiteTerm_isModuleCompact u hu i)

end BC4lean.KKTheory
