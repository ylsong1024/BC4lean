import BC4lean.OddKTheoryLoopDefectPowers
import BC4lean.OddKTheoryMatrixLoopFredholm

/-! # Actual transfer of polynomial multiples of the odd-loop defect

Every power of the genuine matrix pullback multiplied by its square defect
is exactly four actual circle-CFC row entries. The proof transfers the
finite coordinate identities; neither the eigenvalue parameter nor the
separate two-coordinate projection is evaluated at a unitary.
-/

noncomputable section
namespace BC4lean.KKTheory

section ScalarEntries

local instance oddKTheoryLoopDefectPowerTransferScalarOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance oddKTheoryLoopDefectPowerTransferScalarStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-- Scalar evaluation of the four power-defect entries is the actual scalar
loop power times its square defect. -/
theorem oddKTheoryFiniteRowFormula_scalar_power_defect (k : ℕ) (z : Circle) :
    oddKTheoryFiniteRowFormula (oddKTheoryScalarRowAction z)
      (oddKTheoryLoopPowerDefectCircleEntry k)
      (oddKTheoryRowLoopFixedFiniteOperator (B := ℂ) (E := ℂᵐᵒᵖ)) =
        oddKTheoryRowUniversalFredholmLoop (oddKTheoryCircleLoopParameter z) ^ k *
          (oddKTheoryRowUniversalFredholmLoop (oddKTheoryCircleLoopParameter z) *
            oddKTheoryRowUniversalFredholmLoop (oddKTheoryCircleLoopParameter z) - 1) := by
  simp only [oddKTheoryFiniteRowFormula, oddKTheoryScalarRowAction_diagonal,
    smul_mul_assoc, one_mul, oddKTheoryLoopPowerDefectCircleEntry,
    oddKTheoryDescendScalarLoop_apply]
  exact (oddKTheoryRowUniversalFredholmLoop_power_defect_entryFormula k _).symm

/-- The scalar circle entry identity for multiplying the four power-defect
entries by the twenty-one-term genuine loop formula. -/
theorem oddKTheoryLoop_mul_power_defect_circle_entries (k : ℕ) (n m : ℤ) :
    oddKTheoryFiniteCircleEntry
      (fun p : OddKTheoryLoopTerm × Fin 4 =>
        oddKTheoryLoopTermCoefficient p.1 * oddKTheoryLoopPowerDefectCircleEntry k p.2)
      (fun p _ => oddKTheoryLoopTermTarget p.1 (oddKTheoryLoopFiniteTarget p.2))
      (fun p r => oddKTheoryLoopTermWeight p.1 (oddKTheoryLoopFiniteTarget p.2) *
        (if r = oddKTheoryLoopFiniteSource p.2 then 1 else 0)) n m =
      oddKTheoryFiniteCircleEntry (oddKTheoryLoopPowerDefectCircleEntry (k + 1))
        (fun i _ => oddKTheoryLoopFiniteTarget i)
        (fun i r => if r = oddKTheoryLoopFiniteSource i then 1 else 0) n m := by
  ext z
  let A := oddKTheoryRowLoopTermOperator (B := ℂ) (E := ℂᵐᵒᵖ)
  let C := oddKTheoryRowLoopFixedFiniteOperator (B := ℂ) (E := ℂᵐᵒᵖ)
  have hprod := fun p : OddKTheoryLoopTerm × Fin 4 =>
    oddKTheoryRowCoordinateRule_mul (A p.1) (C p.2)
      (oddKTheoryLoopTermTarget p.1) (fun _ => oddKTheoryLoopFiniteTarget p.2)
      (oddKTheoryLoopTermWeight p.1)
      (fun r => if r = oddKTheoryLoopFiniteSource p.2 then 1 else 0)
      (oddKTheoryRowLoopTermOperator_coordinateRule p.1)
      (oddKTheoryRowLoopFixedFiniteOperator_coordinateRule p.2)
  rw [← oddKTheoryFiniteRowFormula_scalar_entry _ (fun p => A p.1 * C p.2)
      _ _ hprod z n m,
    ← oddKTheoryFiniteRowFormula_scalar_entry _ C _ _
      oddKTheoryRowLoopFixedFiniteOperator_coordinateRule z n m]
  have hop : oddKTheoryFiniteRowFormula (oddKTheoryScalarRowAction z)
      (fun p : OddKTheoryLoopTerm × Fin 4 =>
        oddKTheoryLoopTermCoefficient p.1 * oddKTheoryLoopPowerDefectCircleEntry k p.2)
      (fun p => A p.1 * C p.2) =
      oddKTheoryFiniteRowFormula (oddKTheoryScalarRowAction z)
        (oddKTheoryLoopPowerDefectCircleEntry (k + 1)) C := by
    rw [← oddKTheoryFiniteRowFormula_mul]
    · rw [oddKTheoryFiniteRowFormula_scalar_loop,
        oddKTheoryFiniteRowFormula_scalar_power_defect,
        oddKTheoryFiniteRowFormula_scalar_power_defect, pow_succ', mul_assoc]
    · intro i j
      exact oddKTheoryRowLoopTermOperator_diagonal_commute i _
  rw [hop]

end ScalarEntries

section ActualTransfer

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

/-- Exact genuine row coefficient transfer for the multiplication recursion
of the periodic power-defect entries. -/
theorem oddKTheoryFiniteRowFormula_loop_mul_power_defect
    (φ : C(Circle, ℂ) →⋆ₐ[ℂ] AdjointableMap B E E) (k : ℕ) :
    oddKTheoryFiniteRowFormula φ oddKTheoryLoopTermCoefficient oddKTheoryRowLoopTermOperator *
        oddKTheoryFiniteRowFormula φ (oddKTheoryLoopPowerDefectCircleEntry k)
          oddKTheoryRowLoopFixedFiniteOperator =
      oddKTheoryFiniteRowFormula φ (oddKTheoryLoopPowerDefectCircleEntry (k + 1))
        oddKTheoryRowLoopFixedFiniteOperator := by
  rw [oddKTheoryFiniteRowFormula_mul φ _ _ _ _
    (fun i _ => oddKTheoryRowLoopTermOperator_diagonal_commute i _)]
  have hprod := fun p : OddKTheoryLoopTerm × Fin 4 =>
    oddKTheoryRowCoordinateRule_mul
      (oddKTheoryRowLoopTermOperator (B := B) (E := E) p.1)
      (oddKTheoryRowLoopFixedFiniteOperator p.2)
      (oddKTheoryLoopTermTarget p.1) (fun _ => oddKTheoryLoopFiniteTarget p.2)
      (oddKTheoryLoopTermWeight p.1)
      (fun r => if r = oddKTheoryLoopFiniteSource p.2 then 1 else 0)
      (oddKTheoryRowLoopTermOperator_coordinateRule p.1)
      (oddKTheoryRowLoopFixedFiniteOperator_coordinateRule p.2)
  exact oddKTheoryFiniteRowFormula_transfer φ _ _ _ _ hprod
    (oddKTheoryLoopPowerDefectCircleEntry (k + 1)) oddKTheoryRowLoopFixedFiniteOperator
    (fun i _ => oddKTheoryLoopFiniteTarget i)
    (fun i r => if r = oddKTheoryLoopFiniteSource i then 1 else 0)
    oddKTheoryRowLoopFixedFiniteOperator_coordinateRule
    (oddKTheoryLoop_mul_power_defect_circle_entries k)

/-- Every genuine operator power times the square defect has the four
actual periodic entry formula, after any genuine row coefficient action. -/
theorem oddKTheoryFiniteRowFormula_loop_pow_mul_square_defect
    (φ : C(Circle, ℂ) →⋆ₐ[ℂ] AdjointableMap B E E) (k : ℕ) :
    oddKTheoryFiniteRowFormula φ oddKTheoryLoopTermCoefficient oddKTheoryRowLoopTermOperator ^ k *
        (oddKTheoryFiniteRowFormula φ oddKTheoryLoopTermCoefficient oddKTheoryRowLoopTermOperator *
          oddKTheoryFiniteRowFormula φ oddKTheoryLoopTermCoefficient oddKTheoryRowLoopTermOperator - 1) =
      oddKTheoryFiniteRowFormula φ (oddKTheoryLoopPowerDefectCircleEntry k)
        oddKTheoryRowLoopFixedFiniteOperator := by
  induction k with
  | zero =>
    rw [pow_zero, one_mul, oddKTheoryFiniteRowFormula_loop_square]
    simp only [add_sub_cancel_left, oddKTheoryFiniteRowFormula,
      oddKTheoryLoopPowerDefectCircleEntry_pow_zero]
  | succ k ih =>
    rw [pow_succ', mul_assoc, ih, oddKTheoryFiniteRowFormula_loop_mul_power_defect]

end ActualTransfer

section MatrixPullback

variable {B ι : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [DecidableEq ι]

/-- Exact four-entry formula for powers of the actual matrix-unitary
Fredholm pullback times its actual square defect. -/
theorem oddKTheoryMatrixLoopPullback_pow_mul_square_defect
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) (k : ℕ) :
    oddKTheoryMatrixLoopPullback u ^ k *
        (oddKTheoryMatrixLoopPullback u * oddKTheoryMatrixLoopPullback u - 1) =
      ∑ i : Fin 4, oddKTheoryMatrixCircleCoefficient u (oddKTheoryLoopPowerDefectCircleEntry k i) *
        oddKTheoryRowLoopFixedFiniteOperator i := by
  rw [oddKTheoryMatrixLoopPullback_finiteFormula,
    oddKTheoryFiniteRowFormula_loop_pow_mul_square_defect]
  rfl

end MatrixPullback
end BC4lean.KKTheory
