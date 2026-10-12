import BC4lean.OddKTheoryMatrixLoopExponential
import BC4lean.OddKTheoryOperatorK1Recovery
import BC4lean.OddKTheoryFiniteCoordinateEquiv

/-! # The actual two-row corner of the infinite exponential

The two distinguished integer rows 0 and -1 give an adjointable isometric
embedding of B^(ι ⊕ ι) in the completed row module. The genuine exponential
defect is exactly the embedded four-entry finite recovery matrix defect.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped CStarAlgebra

section Pair

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

def oddKTheoryTwoRowPairInclusion :
    AdjointableMap B (HilbertModuleSum B E E) (CountableHilbertModuleSum B E) :=
  (countableModuleInclusion 0).comp sumFst + (countableModuleInclusion 1).comp sumSnd

@[simp] theorem oddKTheoryTwoRowPairInclusion_apply (x : HilbertModuleSum B E E) :
    oddKTheoryTwoRowPairInclusion x = countableModuleInclusion 0 x.fst +
      countableModuleInclusion 1 x.snd := rfl

@[simp] theorem oddKTheoryTwoRowPairInclusion_adjoint_apply (x : CountableHilbertModuleSum B E) :
    oddKTheoryTwoRowPairInclusion.adjoint x =
      sumMk (countableModuleEvaluation 0 x) (countableModuleEvaluation 1 x) := by
  change sumMk (countableModuleEvaluation 0 x) (0 : E) +
    sumMk (0 : E) (countableModuleEvaluation 1 x) = _
  rw [sumMk_add]
  simp only [add_zero, zero_add]

theorem oddKTheoryTwoRowPairInclusion_isometry :
    (oddKTheoryTwoRowPairInclusion (B := B) (E := E)).adjoint.comp
      oddKTheoryTwoRowPairInclusion = AdjointableMap.id := by
  apply AdjointableMap.ext
  intro x
  apply Prod.ext
  all_goals
    simp only [AdjointableMap.comp_apply, oddKTheoryTwoRowPairInclusion_apply,
      oddKTheoryTwoRowPairInclusion_adjoint_apply, sumMk_fst, sumMk_snd, map_add,
      countableModuleEvaluation_inclusion, if_pos rfl, if_neg (by decide : (1 : ℕ) ≠ 0),
      if_neg (by decide : (0 : ℕ) ≠ 1), add_zero, zero_add, AdjointableMap.id_apply]

end Pair

variable {B ι : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [DecidableEq ι]

local instance oddContinuationOddKTheoryTwoRowExponentialCornerLocalInstance01 : CompleteSpace (FiniteStandardModule B ι) := finiteStandardModule_complete
local instance oddContinuationOddKTheoryTwoRowExponentialCornerLocalInstance02 : CompleteSpace (FiniteStandardModule B (ι ⊕ ι)) := finiteStandardModule_complete
local instance oddContinuationOddKTheoryTwoRowExponentialCornerLocalInstance03 : CompleteSpace (HilbertModuleSum B (FiniteStandardModule B ι)
    (FiniteStandardModule B ι)) := hilbertModuleSum_complete

def oddKTheoryTwoRowFiniteInclusion :
    AdjointableMap B (FiniteStandardModule B (ι ⊕ ι))
      (CountableHilbertModuleSum B (FiniteStandardModule B ι)) :=
  oddKTheoryTwoRowPairInclusion.comp oddKTheoryFiniteSumEquiv.toAdjointable

@[simp] theorem oddKTheoryTwoRowFiniteInclusion_apply (x : FiniteStandardModule B (ι ⊕ ι)) :
    oddKTheoryTwoRowFiniteInclusion x =
      countableModuleInclusion 0 (oddKTheoryFiniteSumEquiv x).fst +
        countableModuleInclusion 1 (oddKTheoryFiniteSumEquiv x).snd := rfl

@[simp] theorem oddKTheoryTwoRowFiniteInclusion_adjoint_apply
    (x : CountableHilbertModuleSum B (FiniteStandardModule B ι)) :
    oddKTheoryTwoRowFiniteInclusion.adjoint x = oddKTheoryFiniteSumEquiv.symm
        (sumMk (countableModuleEvaluation 0 x) (countableModuleEvaluation 1 x)) := by
  change oddKTheoryFiniteSumEquiv.symm (oddKTheoryTwoRowPairInclusion.adjoint x) = _
  rw [oddKTheoryTwoRowPairInclusion_adjoint_apply]

theorem oddKTheoryTwoRowFiniteInclusion_isometry :
    (oddKTheoryTwoRowFiniteInclusion (B := B) (ι := ι)).adjoint.comp
      oddKTheoryTwoRowFiniteInclusion = AdjointableMap.id := by
  apply AdjointableMap.ext
  intro x
  apply oddKTheoryFiniteSumEquiv.injective
  simp only [AdjointableMap.comp_apply, oddKTheoryTwoRowFiniteInclusion_apply,
    oddKTheoryTwoRowFiniteInclusion_adjoint_apply, HilbertModuleEquiv.apply_symm_apply,
    AdjointableMap.id_apply]
  apply Prod.ext
  all_goals
    simp only [sumMk_fst, sumMk_snd, map_add, countableModuleEvaluation_inclusion,
      if_pos rfl, if_neg (by decide : (1 : ℕ) ≠ 0),
      if_neg (by decide : (0 : ℕ) ≠ 1), add_zero, zero_add]

theorem oddKTheoryTwoBlockRepresentation_apply
    (A C D H : CStarMatrix ι ι (Unitization ℂ B)) (x : FiniteStandardModule B (ι ⊕ ι)) :
    oddKTheoryFiniteSumEquiv
      (unitizedModuleMatrixRepresentation
        (oddKTheoryTwoBlockFlatten (CStarMatrix.ofMatrix ![![A, C], ![D, H]])) x) =
      sumMk (unitizedModuleMatrixRepresentation A (oddKTheoryFiniteSumEquiv x).fst +
          unitizedModuleMatrixRepresentation C (oddKTheoryFiniteSumEquiv x).snd)
        (unitizedModuleMatrixRepresentation D (oddKTheoryFiniteSumEquiv x).fst +
          unitizedModuleMatrixRepresentation H (oddKTheoryFiniteSumEquiv x).snd) := by
  apply Prod.ext <;> ext i
  all_goals
    simp only [oddKTheoryFiniteSumEquiv, oddKTheoryFiniteSumLinear,
      unitizedModuleMatrixRepresentation_apply, oddKTheoryTwoBlockFlatten_inl_inl,
      oddKTheoryTwoBlockFlatten_inl_inr, oddKTheoryTwoBlockFlatten_inr_inl,
      oddKTheoryTwoBlockFlatten_inr_inr, CStarMatrix.ofMatrix_apply,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons,
      Fintype.sum_sum_type, sumMk_fst, sumMk_snd]

theorem oddKTheoryRecoveryOperator_defect_pair
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) (x : FiniteStandardModule B (ι ⊕ ι)) :
    oddKTheoryFiniteSumEquiv
      ((unitizedModuleMatrixRepresentation (oddKTheoryFiniteExponentialRecovery u) - 1) x) =
      sumMk
        (unitizedModuleMatrixRepresentation (oddKTheoryCircleCFC u (oddKTheoryLoopExponentialCircleEntry 0))
            (oddKTheoryFiniteSumEquiv x).fst +
          unitizedModuleMatrixRepresentation (oddKTheoryCircleCFC u (oddKTheoryLoopExponentialCircleEntry 1))
            (oddKTheoryFiniteSumEquiv x).snd)
        (unitizedModuleMatrixRepresentation (oddKTheoryCircleCFC u (oddKTheoryLoopExponentialCircleEntry 2))
            (oddKTheoryFiniteSumEquiv x).fst +
          unitizedModuleMatrixRepresentation (oddKTheoryCircleCFC u (oddKTheoryLoopExponentialCircleEntry 3))
            (oddKTheoryFiniteSumEquiv x).snd) := by
  rw [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, HilbertModuleEquiv.map_sub,
    oddKTheoryFiniteExponentialRecovery_entryMatrix, oddKTheoryTwoBlockRepresentation_apply]
  simp only [map_add, oddKTheoryUnitizedRowMatrix_one, AdjointableMap.coe_add_apply,
    AdjointableMap.one_apply]
  apply Prod.ext <;> change (_ + _ + _) - _ = _ <;> abel

theorem oddKTheoryTwoRowFiniteInclusion_adjoint_integer
    (z : ℤ) (x : FiniteStandardModule B ι) :
    oddKTheoryTwoRowFiniteInclusion.adjoint (oddKTheoryRowIntegerInclusion z x) =
      oddKTheoryFiniteSumEquiv.symm
        (sumMk (if z = 0 then x else 0) (if z = -1 then x else 0)) := by
  rw [oddKTheoryTwoRowFiniteInclusion_adjoint_apply]
  congr 1
  apply Prod.ext
  · have hz : oddKTheoryRowIntegerIndex z = 0 ↔ z = 0 := by
      change Equiv.intEquivNat z = Equiv.intEquivNat 0 ↔ _
      exact Equiv.intEquivNat.injective.eq_iff
    simp only [oddKTheoryRowIntegerInclusion, countableModuleEvaluation_inclusion, hz]
  · simp only [oddKTheoryRowIntegerInclusion, countableModuleEvaluation_inclusion]
    have hz : oddKTheoryRowIntegerIndex z = 1 ↔ z = -1 := by
      change Equiv.intEquivNat z = Equiv.intEquivNat (-1) ↔ _
      exact Equiv.intEquivNat.injective.eq_iff
    simp only [hz]

theorem oddKTheoryMatrixLoopExponential_twoRowCorner
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) :
    (oddFredholmExponential (oddKTheoryMatrixLoopSelfAdjoint u) : OddKTheoryMatrixRowOperator B ι) - 1 =
      (oddKTheoryTwoRowFiniteInclusion.comp
        (unitizedModuleMatrixRepresentation (oddKTheoryFiniteExponentialRecovery u) - 1)).comp
          oddKTheoryTwoRowFiniteInclusion.adjoint := by
  rw [oddKTheoryMatrixLoopPullback_exponential_sub_one]
  apply oddKTheoryRowOperator_ext_integerCoordinates
  intro z x
  rw [AdjointableMap.comp_apply, AdjointableMap.comp_apply,
    oddKTheoryTwoRowFiniteInclusion_adjoint_integer, oddKTheoryTwoRowFiniteInclusion_apply,
    oddKTheoryRecoveryOperator_defect_pair, HilbertModuleEquiv.apply_symm_apply]
  simp only [oddKTheoryRowLoopFixedFiniteOperator, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons,
    AdjointableMap.coe_add_apply, AdjointableMap.mul_apply,
    oddKTheoryRowReflectionOperator_inclusion, oddKTheoryRowZeroProjection_inclusion,
    oddKTheoryMatrixCircleCoefficient, oddKTheoryCountableRowMatrixHom,
    oddKTheoryRowDiagonal_integerInclusion]
  by_cases hz0 : z = 0
  · subst z
    simp only [if_pos rfl, if_neg (by norm_num : (0 : ℤ) ≠ -1), zero_add,
      sub_zero, neg_zero, zero_smul, map_zero, add_zero, zero_add]
    rfl
  · by_cases hz1 : z = -1
    · subst z
      norm_num [oddKTheoryRowIntegerInclusion, oddKTheoryRowIntegerIndex]
    · have hz' : -z + -1 ≠ 0 := by omega
      simp only [if_neg hz0, if_neg hz1, if_neg hz', map_zero,
        AdjointableMap.coe_zero_apply, zero_add, add_zero]

end BC4lean.KKTheory
