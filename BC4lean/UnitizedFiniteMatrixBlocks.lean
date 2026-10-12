import BC4lean.OddKTheoryFiniteCoordinateEquiv
import BC4lean.UnitizedFiniteModuleOperator

/-! # The actual four-block unitization matrix action

The genuine finite-coordinate unitary identifies the whole paired finite
module with its two summands. Arbitrary four-block unitization matrices then
act by their actual coordinate operators, including their scalar identity
parts over a possibly nonunital coefficient algebra.
-/

noncomputable section
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory
open scoped Matrix

set_option synthInstance.maxSize 512

variable {B : Type*} {ι : Type} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [DecidableEq ι]

local instance unitizedFiniteFourBlockFiniteComplete :
    CompleteSpace (FiniteStandardModule B ι) := finiteStandardModule_complete
local instance unitizedFiniteFourBlockSumComplete :
    CompleteSpace (HilbertModuleSum B (FiniteStandardModule B ι) (FiniteStandardModule B ι)) :=
  hilbertModuleSum_complete

def unitizedFiniteFourBlockMatrix (A D S T : CStarMatrix ι ι (Unitization ℂ B)) :
    CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B) :=
  CStarMatrix.ofMatrix (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm A)
    (CStarMatrix.ofMatrix.symm S) (CStarMatrix.ofMatrix.symm T) (CStarMatrix.ofMatrix.symm D))

def finiteModuleFourBlockOperator
    (A D S T : AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι)) :
    AdjointableMap B (HilbertModuleSum B (FiniteStandardModule B ι) (FiniteStandardModule B ι))
      (HilbertModuleSum B (FiniteStandardModule B ι) (FiniteStandardModule B ι)) :=
  sumMap A D + ((sumInl.comp S).comp sumSnd + (sumInr.comp T).comp sumFst)

omit [DecidableEq ι] in
@[simp] theorem finiteModuleFourBlockOperator_apply
    (A D S T : AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι))
    (x : HilbertModuleSum B (FiniteStandardModule B ι) (FiniteStandardModule B ι)) :
    finiteModuleFourBlockOperator A D S T x = sumMk (B := B) (A x.fst + S x.snd) (T x.fst + D x.snd) := by
  simp only [finiteModuleFourBlockOperator, AdjointableMap.coe_add_apply,
    AdjointableMap.comp_apply, sumMap_apply, sumInl_apply, sumInr_apply,
    sumSnd_apply, sumFst_apply, sumMk_add, add_zero, zero_add]
  rw [add_comm (D x.snd) (T x.fst)]

theorem unitizedModuleMatrixRepresentation_fourBlocks
    (A D S T : CStarMatrix ι ι (Unitization ℂ B)) :
    (oddKTheoryFiniteSumEquiv (B := B) (ι := ι) (κ := ι)).transport
      (unitizedModuleMatrixRepresentation (unitizedFiniteFourBlockMatrix A D S T)) =
        finiteModuleFourBlockOperator (unitizedModuleMatrixRepresentation A)
          (unitizedModuleMatrixRepresentation D) (unitizedModuleMatrixRepresentation S)
          (unitizedModuleMatrixRepresentation T) := by
  ext x
  rw [HilbertModuleEquiv.transport_apply, finiteModuleFourBlockOperator_apply]
  apply Prod.ext
  · ext i
    change unitizedModuleMatrixRepresentation (unitizedFiniteFourBlockMatrix A D S T)
      ((WithCStarModule.equiv Bᵐᵒᵖ ((ι ⊕ ι) → Bᵐᵒᵖ)).symm (Sum.elim x.fst x.snd))
      (Sum.inl i) =
      (unitizedModuleMatrixRepresentation A x.fst + unitizedModuleMatrixRepresentation S x.snd) i
    simp only [unitizedModuleMatrixRepresentation_apply, WithCStarModule.add_apply]
    change (∑ j : ι ⊕ ι, unitizedStandardLeftMul
      (unitizedFiniteFourBlockMatrix A D S T (Sum.inl i) j) (Sum.elim x.fst x.snd j)) =
        (∑ j : ι, unitizedStandardLeftMul (A i j) (x.fst j)) +
          (∑ j : ι, unitizedStandardLeftMul (S i j) (x.snd j))
    rw [Fintype.sum_sum_type]
    rfl
  · ext i
    change unitizedModuleMatrixRepresentation (unitizedFiniteFourBlockMatrix A D S T)
      ((WithCStarModule.equiv Bᵐᵒᵖ ((ι ⊕ ι) → Bᵐᵒᵖ)).symm (Sum.elim x.fst x.snd))
      (Sum.inr i) =
      (unitizedModuleMatrixRepresentation T x.fst + unitizedModuleMatrixRepresentation D x.snd) i
    simp only [unitizedModuleMatrixRepresentation_apply, WithCStarModule.add_apply]
    change (∑ j : ι ⊕ ι, unitizedStandardLeftMul
      (unitizedFiniteFourBlockMatrix A D S T (Sum.inr i) j) (Sum.elim x.fst x.snd j)) =
        (∑ j : ι, unitizedStandardLeftMul (T i j) (x.fst j)) +
          (∑ j : ι, unitizedStandardLeftMul (D i j) (x.snd j))
    rw [Fintype.sum_sum_type]
    rfl

end BC4lean.KKTheory
