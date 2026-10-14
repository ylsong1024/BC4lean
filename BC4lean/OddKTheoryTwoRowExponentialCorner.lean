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

set_option synthInstance.maxSize 512

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
  rw [AdjointableMap.comp_apply, oddKTheoryTwoRowPairInclusion_apply,
    oddKTheoryTwoRowPairInclusion_adjoint_apply]
  simpa only [map_add, countableModuleEvaluation_inclusion, if_true,
    if_neg (by decide : (1 : ℕ) ≠ 0), if_neg (by decide : (0 : ℕ) ≠ 1),
    add_zero, zero_add, AdjointableMap.id_apply] using (sumMk_eta x)

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

omit [DecidableEq ι] in
@[simp] theorem oddKTheoryTwoRowFiniteInclusion_apply (x : FiniteStandardModule B (ι ⊕ ι)) :
    oddKTheoryTwoRowFiniteInclusion x =
      countableModuleInclusion 0 (oddKTheoryFiniteSumEquiv x).fst +
        countableModuleInclusion 1 (oddKTheoryFiniteSumEquiv x).snd := rfl

omit [DecidableEq ι] in
@[simp] theorem oddKTheoryTwoRowFiniteInclusion_adjoint_apply
    (x : CountableHilbertModuleSum B (FiniteStandardModule B ι)) :
    oddKTheoryTwoRowFiniteInclusion.adjoint x = oddKTheoryFiniteSumEquiv.symm
        (sumMk (countableModuleEvaluation 0 x) (countableModuleEvaluation 1 x)) := by
  change oddKTheoryFiniteSumEquiv.symm (oddKTheoryTwoRowPairInclusion.adjoint x) = _
  rw [oddKTheoryTwoRowPairInclusion_adjoint_apply]

omit [DecidableEq ι] in
theorem oddKTheoryTwoRowFiniteInclusion_isometry :
    (oddKTheoryTwoRowFiniteInclusion (B := B) (ι := ι)).adjoint.comp
      oddKTheoryTwoRowFiniteInclusion = AdjointableMap.id := by
  apply AdjointableMap.ext
  intro x
  let e := oddKTheoryFiniteSumEquiv (B := B) (ι := ι) (κ := ι)
  let P := oddKTheoryTwoRowPairInclusion (B := B) (E := FiniteStandardModule B ι)
  have hp : P.adjoint (P (e x)) = e x := by
    have h := congrArg
      (fun T : AdjointableMap B
        (HilbertModuleSum B (FiniteStandardModule B ι) (FiniteStandardModule B ι))
        (HilbertModuleSum B (FiniteStandardModule B ι) (FiniteStandardModule B ι)) => T (e x))
      (oddKTheoryTwoRowPairInclusion_isometry (B := B) (E := FiniteStandardModule B ι))
    simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply] using h
  change e.symm (P.adjoint (P (e x))) = x
  rw [hp]
  exact e.symm_apply_apply x

theorem oddKTheoryTwoBlockRepresentation_apply
    (A C D H : CStarMatrix ι ι (Unitization ℂ B)) (x : FiniteStandardModule B (ι ⊕ ι)) :
    oddKTheoryFiniteSumEquiv
      (unitizedModuleMatrixRepresentation
        (oddKTheoryTwoBlockFlatten (CStarMatrix.ofMatrix ![![A, C], ![D, H]])) x) =
      sumMk (unitizedModuleMatrixRepresentation A (oddKTheoryFiniteSumEquiv x).fst +
          unitizedModuleMatrixRepresentation C (oddKTheoryFiniteSumEquiv x).snd)
        (unitizedModuleMatrixRepresentation D (oddKTheoryFiniteSumEquiv x).fst +
          unitizedModuleMatrixRepresentation H (oddKTheoryFiniteSumEquiv x).snd) := by
  apply Prod.ext
  · ext i
    change unitizedModuleMatrixRepresentation
      (oddKTheoryTwoBlockFlatten (CStarMatrix.ofMatrix
        (![![A, C], ![D, H]] : Matrix (Fin 2) (Fin 2) (CStarMatrix ι ι (Unitization ℂ B)))))
      x (Sum.inl i) =
        (unitizedModuleMatrixRepresentation A (oddKTheoryFiniteSumEquiv x).fst +
          unitizedModuleMatrixRepresentation C (oddKTheoryFiniteSumEquiv x).snd) i
    simp only [unitizedModuleMatrixRepresentation_apply, WithCStarModule.add_apply]
    rw [Fintype.sum_sum_type]
    rfl
  · ext i
    change unitizedModuleMatrixRepresentation
      (oddKTheoryTwoBlockFlatten (CStarMatrix.ofMatrix
        (![![A, C], ![D, H]] : Matrix (Fin 2) (Fin 2) (CStarMatrix ι ι (Unitization ℂ B)))))
      x (Sum.inr i) =
        (unitizedModuleMatrixRepresentation D (oddKTheoryFiniteSumEquiv x).fst +
          unitizedModuleMatrixRepresentation H (oddKTheoryFiniteSumEquiv x).snd) i
    simp only [unitizedModuleMatrixRepresentation_apply, WithCStarModule.add_apply]
    rw [Fintype.sum_sum_type]
    rfl

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
  apply Prod.ext
  · simp only [WithCStarModule.sub_fst, sumMk_fst]
    abel
  · simp only [WithCStarModule.sub_snd, sumMk_snd]
    abel

omit [DecidableEq ι] in
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
    simp only [oddKTheoryRowIntegerInclusion, countableModuleEvaluation_inclusion, hz, sumMk_fst]
  · simp only [oddKTheoryRowIntegerInclusion, countableModuleEvaluation_inclusion]
    have hz : oddKTheoryRowIntegerIndex z = 1 ↔ z = -1 := by
      change Equiv.intEquivNat z = Equiv.intEquivNat (-1) ↔ _
      exact Equiv.intEquivNat.injective.eq_iff
    simp only [hz, sumMk_snd]

set_option maxHeartbeats 8000000 in
theorem oddKTheoryMatrixLoopExponential_twoRowCorner
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) :
    (oddFredholmExponential (A := OddKTheoryMatrixRowOperator B ι)
      (oddKTheoryMatrixLoopSelfAdjoint (B := B) (ι := ι) u) : OddKTheoryMatrixRowOperator B ι) - 1 =
      ((oddKTheoryTwoRowFiniteInclusion (B := B) (ι := ι)).comp
        (unitizedModuleMatrixRepresentation
          (oddKTheoryFiniteExponentialRecovery (A := Unitization ℂ B) (ι := ι) u) - 1)).comp
          (oddKTheoryTwoRowFiniteInclusion (B := B) (ι := ι)).adjoint := by
  have hcoeff (f : C(Circle, ℂ)) (n : ℕ) (y : FiniteStandardModule B ι) :
      oddKTheoryMatrixCircleCoefficient u f (countableModuleInclusion n y) =
        countableModuleInclusion n (unitizedModuleMatrixRepresentation (oddKTheoryCircleCFC u f) y) := by
    change countableModuleDiagonal
      (unitizedModuleMatrixRepresentation (oddKTheoryCircleCFC u f))
      (countableModuleInclusion n y) = _
    exact oddKTheoryCountableDiagonal_inclusion _ n y
  have hcoeffInteger (f : C(Circle, ℂ)) (k : ℤ) (y : FiniteStandardModule B ι) :
      oddKTheoryMatrixCircleCoefficient u f (oddKTheoryRowIntegerInclusion k y) =
        oddKTheoryRowIntegerInclusion k
          (unitizedModuleMatrixRepresentation (oddKTheoryCircleCFC u f) y) :=
    hcoeff f (oddKTheoryRowIntegerIndex k) y
  have h0 := oddKTheoryRowLoopFixedFiniteOperator_matrixUnit (B := B) (ι := ι) (0 : Fin 4)
  have h1 := oddKTheoryRowLoopFixedFiniteOperator_matrixUnit (B := B) (ι := ι) (1 : Fin 4)
  have h2 := oddKTheoryRowLoopFixedFiniteOperator_matrixUnit (B := B) (ι := ι) (2 : Fin 4)
  have h3 := oddKTheoryRowLoopFixedFiniteOperator_matrixUnit (B := B) (ι := ι) (3 : Fin 4)
  change oddKTheoryRowLoopFixedFiniteOperator (B := B) (E := FiniteStandardModule B ι) 0 =
    oddKTheoryRowIntegerMatrixUnit (B := B) (ι := ι) 0 0 at h0
  change oddKTheoryRowLoopFixedFiniteOperator (B := B) (E := FiniteStandardModule B ι) 1 =
    oddKTheoryRowIntegerMatrixUnit (B := B) (ι := ι) 0 (-1) at h1
  change oddKTheoryRowLoopFixedFiniteOperator (B := B) (E := FiniteStandardModule B ι) 2 =
    oddKTheoryRowIntegerMatrixUnit (B := B) (ι := ι) (-1) 0 at h2
  change oddKTheoryRowLoopFixedFiniteOperator (B := B) (E := FiniteStandardModule B ι) 3 =
    oddKTheoryRowIntegerMatrixUnit (B := B) (ι := ι) (-1) (-1) at h3
  rw [oddKTheoryMatrixLoopPullback_exponential_sub_one]
  apply oddKTheoryRowOperator_ext_integerCoordinates
  intro z x
  rw [AdjointableMap.comp_apply, AdjointableMap.comp_apply,
    oddKTheoryTwoRowFiniteInclusion_adjoint_integer, oddKTheoryTwoRowFiniteInclusion_apply,
    oddKTheoryRecoveryOperator_defect_pair, HilbertModuleEquiv.apply_symm_apply]
  simp only [Fin.sum_univ_four, AdjointableMap.coe_add_apply, AdjointableMap.mul_apply,
    h0, h1, h2, h3, oddKTheoryRowIntegerMatrixUnit_inclusion, sumMk_fst, sumMk_snd]
  by_cases hz0 : z = 0
  · subst z
    simp only [if_true, if_neg (by decide : (0 : ℤ) ≠ -1), map_zero,
      add_zero, hcoeffInteger]
    rfl
  · by_cases hz1 : z = -1
    · subst z
      simp only [if_true, if_neg (by decide : (-1 : ℤ) ≠ 0), map_zero,
        zero_add, add_zero, hcoeffInteger]
      rfl
    · simp only [if_neg hz0, if_neg hz1, map_zero, add_zero]

end BC4lean.KKTheory
