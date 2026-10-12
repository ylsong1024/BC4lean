import BC4lean.OddKTheoryLoopSquareTransfer

/-! # Periodic polynomial multiples of the genuine loop defect

The scalar loop has F(F²-I)=(2t-1)(F²-I). Multiplication by the
vanishing square defect makes each power coefficient periodic even though
the separate eigenvalue parameter and projection are not periodic. This
module records the actual interval operator identities and the descended
four-entry formulas needed for polynomial functional calculus transfer.
-/

noncomputable section
namespace BC4lean.KKTheory

section ActualInterval

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

/-- The crossing operator has the stated eigenvalue on its genuine zero row. -/
theorem oddKTheoryRowCrossingOperator_mul_zeroProjection (t : ℝ) :
    oddKTheoryRowCrossingOperator (B := B) (E := E) t * oddKTheoryRowZeroProjection =
      (2 * (t : ℂ) - 1) • oddKTheoryRowZeroProjection := by
  rw [oddKTheoryRowCrossingOperator, add_mul, smul_mul_assoc,
    oddKTheoryRowSign_mul_zeroProjection, oddKTheoryRowZeroProjection_square]
  module

/-- The genuine scalar-loop square defect is an eigenoperator for left
multiplication by the actual infinite Fredholm loop. -/
theorem oddKTheoryRowUniversalFredholmLoop_mul_square_defect (t : ℝ) :
    oddKTheoryRowUniversalFredholmLoop (B := B) (E := E) t *
        (oddKTheoryRowUniversalFredholmLoop t * oddKTheoryRowUniversalFredholmLoop t - 1) =
      (2 * (t : ℂ) - 1) •
        (oddKTheoryRowUniversalFredholmLoop t * oddKTheoryRowUniversalFredholmLoop t - 1) := by
  let V := oddKTheoryRowLoopConjugator (B := B) (E := E) t
  let P := oddKTheoryRowZeroProjection (B := B) (E := E)
  have hVP : oddKTheoryRowUniversalFredholmLoop t *
      (star (V : OddKTheoryCountableOperator B E) * P * (V : OddKTheoryCountableOperator B E)) =
      (2 * (t : ℂ) - 1) • (star (V : OddKTheoryCountableOperator B E) * P * (V : OddKTheoryCountableOperator B E)) := by
    change (star (V : OddKTheoryCountableOperator B E) * oddKTheoryRowCrossingOperator t * (V : OddKTheoryCountableOperator B E)) *
      (star (V : OddKTheoryCountableOperator B E) * P * (V : OddKTheoryCountableOperator B E)) = _
    calc
      _ = star (V : OddKTheoryCountableOperator B E) * oddKTheoryRowCrossingOperator t *
          ((V : OddKTheoryCountableOperator B E) * star (V : OddKTheoryCountableOperator B E)) *
            P * (V : OddKTheoryCountableOperator B E) := by simp only [mul_assoc]
      _ = star (V : OddKTheoryCountableOperator B E) *
          (oddKTheoryRowCrossingOperator t * P) * (V : OddKTheoryCountableOperator B E) := by
        have hVV : (V : OddKTheoryCountableOperator B E) *
            star (V : OddKTheoryCountableOperator B E) = 1 :=
          Unitary.coe_mul_star_self V
        rw [hVV, mul_one]
        simp only [mul_assoc]
      _ = _ := by
        rw [oddKTheoryRowCrossingOperator_mul_zeroProjection, mul_smul_comm, smul_mul_assoc]
  rw [oddKTheoryRowUniversalFredholmLoop_square_defect,
    mul_smul_comm, hVP, smul_smul, smul_smul]
  congr 1
  ring

/-- Every actual operator power times the defect is controlled by the
corresponding scalar power, with no division by a nonperiodic function. -/
theorem oddKTheoryRowUniversalFredholmLoop_pow_mul_square_defect (k : ℕ) (t : ℝ) :
    oddKTheoryRowUniversalFredholmLoop (B := B) (E := E) t ^ k *
        (oddKTheoryRowUniversalFredholmLoop t * oddKTheoryRowUniversalFredholmLoop t - 1) =
      (2 * (t : ℂ) - 1) ^ k •
        (oddKTheoryRowUniversalFredholmLoop t * oddKTheoryRowUniversalFredholmLoop t - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, ih, mul_smul_comm,
      oddKTheoryRowUniversalFredholmLoop_mul_square_defect, smul_smul, pow_succ]

end ActualInterval

/-- Powers of the interval eigenvalue occur only multiplied by the actual
vanishing defect entries. -/
def oddKTheoryLoopPowerDefectScalarEntry (k : ℕ) (i : Fin 4) (t : ℝ) : ℂ :=
  (2 * (t : ℂ) - 1) ^ k * oddKTheoryLoopDefectScalarEntries i t

theorem continuous_oddKTheoryLoopPowerDefectScalarEntry (k : ℕ) (i : Fin 4) :
    Continuous (oddKTheoryLoopPowerDefectScalarEntry k i) := by
  unfold oddKTheoryLoopPowerDefectScalarEntry
  have hpower : Continuous (fun t : ℝ => (2 * (t : ℂ) - 1) ^ k) := by fun_prop
  exact hpower.mul (continuous_oddKTheoryLoopDefectScalarEntries i)

@[simp] theorem oddKTheoryLoopPowerDefectScalarEntry_zero (k : ℕ) (i : Fin 4) :
    oddKTheoryLoopPowerDefectScalarEntry k i 0 = 0 := by
  simp [oddKTheoryLoopPowerDefectScalarEntry]

@[simp] theorem oddKTheoryLoopPowerDefectScalarEntry_one (k : ℕ) (i : Fin 4) :
    oddKTheoryLoopPowerDefectScalarEntry k i 1 = 0 := by
  simp [oddKTheoryLoopPowerDefectScalarEntry]

/-- The four genuinely continuous circle entries of the power times defect. -/
def oddKTheoryLoopPowerDefectCircleEntry (k : ℕ) (i : Fin 4) : C(Circle, ℂ) :=
  oddKTheoryDescendScalarLoop (oddKTheoryLoopPowerDefectScalarEntry k i)
    (continuous_oddKTheoryLoopPowerDefectScalarEntry k i) (by simp)

@[simp] theorem oddKTheoryLoopPowerDefectCircleEntry_one (k : ℕ) (i : Fin 4) :
    oddKTheoryLoopPowerDefectCircleEntry k i 1 = 0 := by
  simp [oddKTheoryLoopPowerDefectCircleEntry]

@[simp] theorem oddKTheoryLoopPowerDefectCircleEntry_pow_zero (i : Fin 4) :
    oddKTheoryLoopPowerDefectCircleEntry 0 i = oddKTheoryLoopDefectCircleEntry i := by
  ext z
  simp [oddKTheoryLoopPowerDefectCircleEntry, oddKTheoryLoopDefectCircleEntry,
    oddKTheoryDescendScalarLoop_apply, oddKTheoryLoopPowerDefectScalarEntry]

section EntryFormula

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

/-- Exact actual interval finite-entry formula for every power times defect. -/
theorem oddKTheoryRowUniversalFredholmLoop_power_defect_entryFormula (k : ℕ) (t : ℝ) :
    oddKTheoryRowUniversalFredholmLoop (B := B) (E := E) t ^ k *
        (oddKTheoryRowUniversalFredholmLoop t * oddKTheoryRowUniversalFredholmLoop t - 1) =
      ∑ i : Fin 4, oddKTheoryLoopPowerDefectScalarEntry k i t •
        oddKTheoryRowLoopFixedFiniteOperator i := by
  rw [oddKTheoryRowUniversalFredholmLoop_pow_mul_square_defect,
    oddKTheoryRowUniversalFredholmLoop_square_entryFormula, add_sub_cancel_left]
  simp only [Finset.smul_sum, smul_smul, oddKTheoryLoopPowerDefectScalarEntry]

end EntryFormula
end BC4lean.KKTheory
