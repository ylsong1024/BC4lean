import BC4lean.OddKTheoryFiniteEntryTransfer

/-! # Coordinate rules for the actual universal odd loop

The complete loop consists of twenty-one fixed signed-coordinate terms.
Their coordinate rules are independent of the coefficient Hilbert module.
The square defect has four periodic coefficient functions, each vanishing
at the circle base point. The projection before multiplying by the defect
factor is deliberately not descended to the circle.
-/

noncomputable section
namespace BC4lean.KKTheory

abbrev OddKTheoryLoopTerm := (Fin 4 × Fin 4) ⊕ (Unit ⊕ Fin 4)

def oddKTheoryLoopTermCoefficient : OddKTheoryLoopTerm → C(Circle, ℂ)
  | .inl p => oddKTheoryLoopResidualCircleCoefficient p
  | .inr (.inl _) => oddKTheoryLoopSignCircleCoefficient
  | .inr (.inr i) => oddKTheoryLoopFiniteCircleCoefficient i

def oddKTheoryLoopCoordinatePermutation (i : Fin 4) : ℤ → ℤ :=
  ![id, fun z => -z, fun z => -z - 1, fun z => z + 1] i

def oddKTheoryLoopCoordinateInverse (i : Fin 4) : ℤ → ℤ :=
  ![id, fun z => -z, fun z => -z - 1, fun z => z - 1] i

def oddKTheoryLoopFiniteTarget (i : Fin 4) : ℤ := ![0, 0, -1, -1] i

def oddKTheoryLoopFiniteSource (i : Fin 4) : ℤ := ![0, -1, 0, -1] i

def oddKTheoryLoopTermTarget : OddKTheoryLoopTerm → ℤ → ℤ
  | .inl p, m => oddKTheoryLoopCoordinateInverse p.1 (oddKTheoryLoopCoordinatePermutation p.2 m)
  | .inr (.inl _), m => m
  | .inr (.inr i), _ => oddKTheoryLoopFiniteTarget i

def oddKTheoryLoopTermWeight : OddKTheoryLoopTerm → ℤ → ℂ
  | .inl p, m => oddKTheoryRowIntegerSign (oddKTheoryLoopCoordinatePermutation p.2 m)
  | .inr (.inl _), m => oddKTheoryRowIntegerSign m
  | .inr (.inr i), m => if m = oddKTheoryLoopFiniteSource i then 1 else 0

section ActualRows

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

def oddKTheoryRowLoopTermOperator : OddKTheoryLoopTerm → OddKTheoryCountableOperator B E
  | .inl p => oddKTheoryRowLoopFixedOperator p
  | .inr (.inl _) => oddKTheoryRowSignOperator
  | .inr (.inr i) => oddKTheoryRowLoopFixedFiniteOperator i

/-- The four actual completed coordinate permutations have their stated
integer coordinate actions. -/
theorem oddKTheoryRowLoopFixedPermutation_coordinateRule (i : Fin 4) (m : ℤ) (b : E) :
    oddKTheoryRowLoopFixedPermutation (B := B) (E := E) i (oddKTheoryRowIntegerInclusion m b) =
      oddKTheoryRowIntegerInclusion (oddKTheoryLoopCoordinatePermutation i m) b := by
  fin_cases i
  · rfl
  · change oddKTheoryRowReflectionOperator (B := B) (E := E) 0
      (oddKTheoryRowIntegerInclusion m b) = oddKTheoryRowIntegerInclusion (-m) b
    simpa only [add_zero] using oddKTheoryRowReflectionOperator_inclusion (B := B) 0 m b
  · change oddKTheoryRowReflectionOperator (B := B) (E := E) (-1)
      (oddKTheoryRowIntegerInclusion m b) = oddKTheoryRowIntegerInclusion (-m - 1) b
    simpa only [sub_eq_add_neg] using oddKTheoryRowReflectionOperator_inclusion (B := B) (-1) m b
  · change (oddKTheoryRowReflectionOperator (B := B) (E := E) 0 *
      oddKTheoryRowReflectionOperator (B := B) (E := E) (-1))
      (oddKTheoryRowIntegerInclusion m b) = oddKTheoryRowIntegerInclusion (m + 1) b
    rw [AdjointableMap.mul_apply, oddKTheoryRowReflectionOperator_inclusion,
      oddKTheoryRowReflectionOperator_inclusion]
    have hm : -(-m + (-1)) + 0 = m + 1 := by omega
    rw [hm]

theorem oddKTheoryRowLoopFixedPermutation_star_coordinateRule (i : Fin 4) (m : ℤ) (b : E) :
    star (oddKTheoryRowLoopFixedPermutation (B := B) (E := E) i) (oddKTheoryRowIntegerInclusion m b) =
      oddKTheoryRowIntegerInclusion (oddKTheoryLoopCoordinateInverse i m) b := by
  fin_cases i
  · rfl
  · change (star (oddKTheoryRowReflectionOperator (B := B) (E := E) 0))
      (oddKTheoryRowIntegerInclusion m b) = oddKTheoryRowIntegerInclusion (-m) b
    rw [oddKTheoryRowReflectionOperator_star]
    simpa only [add_zero] using oddKTheoryRowReflectionOperator_inclusion (B := B) 0 m b
  · change (star (oddKTheoryRowReflectionOperator (B := B) (E := E) (-1)))
      (oddKTheoryRowIntegerInclusion m b) = oddKTheoryRowIntegerInclusion (-m - 1) b
    rw [oddKTheoryRowReflectionOperator_star]
    simpa only [sub_eq_add_neg] using oddKTheoryRowReflectionOperator_inclusion (B := B) (-1) m b
  · change (star (oddKTheoryRowReflectionOperator (B := B) (E := E) 0 *
      oddKTheoryRowReflectionOperator (B := B) (E := E) (-1)))
      (oddKTheoryRowIntegerInclusion m b) = oddKTheoryRowIntegerInclusion (m - 1) b
    rw [star_mul, oddKTheoryRowReflectionOperator_star, oddKTheoryRowReflectionOperator_star,
      AdjointableMap.mul_apply, oddKTheoryRowReflectionOperator_inclusion,
      oddKTheoryRowReflectionOperator_inclusion]
    have hm : -(-m + 0) + (-1) = m - 1 := by omega
    rw [hm]

theorem oddKTheoryRowLoopFixedOperator_coordinateRule (p : Fin 4 × Fin 4)
    (m : ℤ) (b : E) :
    oddKTheoryRowLoopFixedOperator (B := B) (E := E) p (oddKTheoryRowIntegerInclusion m b) =
      oddKTheoryRowIntegerInclusion
        (oddKTheoryLoopCoordinateInverse p.1 (oddKTheoryLoopCoordinatePermutation p.2 m))
        (oddKTheoryRowIntegerSign (oddKTheoryLoopCoordinatePermutation p.2 m) • b) := by
  simp only [oddKTheoryRowLoopFixedOperator, AdjointableMap.mul_apply,
    oddKTheoryRowLoopFixedPermutation_coordinateRule, oddKTheoryRowSignOperator_inclusion,
    map_smul (star (oddKTheoryRowLoopFixedPermutation (B := B) (E := E) p.1)).toCLM,
    oddKTheoryRowLoopFixedPermutation_star_coordinateRule, map_smul]

/-- The actual finite coordinate actions hold on every complete row module,
without asserting those coordinate projections compact. -/
theorem oddKTheoryRowLoopFixedFiniteOperator_coordinateRule (i : Fin 4) (m : ℤ) (b : E) :
    oddKTheoryRowLoopFixedFiniteOperator (B := B) (E := E) i (oddKTheoryRowIntegerInclusion m b) =
      oddKTheoryRowIntegerInclusion (oddKTheoryLoopFiniteTarget i)
        ((if m = oddKTheoryLoopFiniteSource i then (1 : ℂ) else 0) • b) := by
  fin_cases i
  · change oddKTheoryRowZeroProjection (B := B) (E := E)
      (oddKTheoryRowIntegerInclusion m b) =
        oddKTheoryRowIntegerInclusion 0 ((if m = 0 then (1 : ℂ) else 0) • b)
    rw [oddKTheoryRowZeroProjection_inclusion]
    split_ifs with h
    · subst m; simp
    · simp
  · change (oddKTheoryRowZeroProjection (B := B) (E := E) *
      oddKTheoryRowReflectionOperator (B := B) (E := E) (-1))
      (oddKTheoryRowIntegerInclusion m b) =
        oddKTheoryRowIntegerInclusion 0 ((if m = -1 then (1 : ℂ) else 0) • b)
    rw [AdjointableMap.mul_apply, oddKTheoryRowReflectionOperator_inclusion,
      oddKTheoryRowZeroProjection_inclusion]
    by_cases h : m = -1
    · subst m; norm_num
    · have hn : -m + (-1) ≠ 0 := by omega
      rw [if_neg hn, if_neg h]
      simp only [zero_smul, map_zero]
  · change (oddKTheoryRowReflectionOperator (B := B) (E := E) (-1) *
      oddKTheoryRowZeroProjection (B := B) (E := E))
      (oddKTheoryRowIntegerInclusion m b) =
        oddKTheoryRowIntegerInclusion (-1) ((if m = 0 then (1 : ℂ) else 0) • b)
    rw [AdjointableMap.mul_apply, oddKTheoryRowZeroProjection_inclusion]
    by_cases h : m = 0
    · subst m; norm_num [oddKTheoryRowReflectionOperator_inclusion]
    · simp only [if_neg h, zero_smul, map_zero]
  · change (oddKTheoryRowReflectionOperator (B := B) (E := E) (-1) *
      oddKTheoryRowZeroProjection (B := B) (E := E) *
      oddKTheoryRowReflectionOperator (B := B) (E := E) (-1))
      (oddKTheoryRowIntegerInclusion m b) =
        oddKTheoryRowIntegerInclusion (-1) ((if m = -1 then (1 : ℂ) else 0) • b)
    rw [AdjointableMap.mul_apply, AdjointableMap.mul_apply,
      oddKTheoryRowReflectionOperator_inclusion, oddKTheoryRowZeroProjection_inclusion]
    by_cases h : m = -1
    · subst m; norm_num [oddKTheoryRowReflectionOperator_inclusion]
    · have hn : -m + (-1) ≠ 0 := by omega
      rw [if_neg hn, if_neg h]
      simp only [map_zero, zero_smul]

theorem oddKTheoryRowLoopTermOperator_coordinateRule (i : OddKTheoryLoopTerm)
    (m : ℤ) (b : E) :
    oddKTheoryRowLoopTermOperator (B := B) (E := E) i (oddKTheoryRowIntegerInclusion m b) =
      oddKTheoryRowIntegerInclusion (oddKTheoryLoopTermTarget i m)
        (oddKTheoryLoopTermWeight i m • b) := by
  cases i with
  | inl p => exact oddKTheoryRowLoopFixedOperator_coordinateRule p m b
  | inr i =>
    cases i with
    | inl _ =>
      simpa only [oddKTheoryRowLoopTermOperator, oddKTheoryLoopTermTarget,
        oddKTheoryLoopTermWeight, map_smul] using oddKTheoryRowSignOperator_inclusion m b
    | inr i => exact oddKTheoryRowLoopFixedFiniteOperator_coordinateRule i m b

theorem oddKTheoryRowLoopTermOperator_diagonal_commute
    (i : OddKTheoryLoopTerm) (S : AdjointableMap B E E) :
    Commute (oddKTheoryRowLoopTermOperator i) (countableModuleDiagonal S) := by
  cases i with
  | inl p => exact oddKTheoryRowLoopFixedOperator_diagonal_commute p S
  | inr i =>
    cases i with
    | inl _ => exact oddKTheoryRowSign_diagonal_commute S
    | inr i => exact oddKTheoryRowLoopFixedFiniteOperator_diagonal_commute i S

end ActualRows

/-- The actual four entries of the two-coordinate scalar projection. These
are used on the interval only; they do not individually descend. -/
def oddKTheoryLoopProjectionScalarEntries (t : ℝ) : Fin 4 → ℂ :=
  let a := oddKTheoryReflectionCoeffA (oddKTheoryHalfPhase t)
  let b := oddKTheoryReflectionCoeffB (oddKTheoryHalfPhase t)
  ![star a * a, star a * b, star b * a, star b * b]

/-- Multiplying by the defect factor produces four genuine periodic entries. -/
def oddKTheoryLoopDefectScalarEntries (i : Fin 4) (t : ℝ) : ℂ :=
  (-4 * (t : ℂ) * (1 - (t : ℂ))) * oddKTheoryLoopProjectionScalarEntries t i

theorem continuous_oddKTheoryLoopDefectScalarEntries (i : Fin 4) :
    Continuous (oddKTheoryLoopDefectScalarEntries i) := by
  fin_cases i
  all_goals
    unfold oddKTheoryLoopDefectScalarEntries oddKTheoryLoopProjectionScalarEntries
    unfold oddKTheoryReflectionCoeffA oddKTheoryReflectionCoeffB
    fun_prop

@[simp] theorem oddKTheoryLoopDefectScalarEntries_zero (i : Fin 4) :
    oddKTheoryLoopDefectScalarEntries i 0 = 0 := by
  simp [oddKTheoryLoopDefectScalarEntries]

@[simp] theorem oddKTheoryLoopDefectScalarEntries_one (i : Fin 4) :
    oddKTheoryLoopDefectScalarEntries i 1 = 0 := by
  simp [oddKTheoryLoopDefectScalarEntries]

def oddKTheoryLoopDefectCircleEntry (i : Fin 4) : C(Circle, ℂ) :=
  oddKTheoryDescendScalarLoop (oddKTheoryLoopDefectScalarEntries i)
    (continuous_oddKTheoryLoopDefectScalarEntries i) (by simp)

@[simp] theorem oddKTheoryLoopDefectCircleEntry_one (i : Fin 4) :
    oddKTheoryLoopDefectCircleEntry i 1 = 0 := by
  simp [oddKTheoryLoopDefectCircleEntry]

section DefectFormula

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

/-- The genuine scalar loop square defect is the four periodic finite entries. -/
theorem oddKTheoryRowUniversalFredholmLoop_square_entryFormula (t : ℝ) :
    oddKTheoryRowUniversalFredholmLoop (B := B) (E := E) t *
        oddKTheoryRowUniversalFredholmLoop t =
      1 + ∑ i : Fin 4, oddKTheoryLoopDefectScalarEntries i t •
        oddKTheoryRowLoopFixedFiniteOperator i := by
  have h := oddKTheoryRowUniversalFredholmLoop_twoCoordinate_square_defect (B := B) (E := E) t
  rw [oddKTheoryRowTwoCoordinateProjection_expansion] at h
  have hexpand :
      (-4 * (t : ℂ) * (1 - (t : ℂ))) •
        ((star (oddKTheoryReflectionCoeffA (oddKTheoryHalfPhase t)) *
          oddKTheoryReflectionCoeffA (oddKTheoryHalfPhase t)) • oddKTheoryRowZeroProjection +
        (star (oddKTheoryReflectionCoeffA (oddKTheoryHalfPhase t)) *
          oddKTheoryReflectionCoeffB (oddKTheoryHalfPhase t)) •
            (oddKTheoryRowZeroProjection * oddKTheoryRowReflectionOperator (-1)) +
        (star (oddKTheoryReflectionCoeffB (oddKTheoryHalfPhase t)) *
          oddKTheoryReflectionCoeffA (oddKTheoryHalfPhase t)) •
            (oddKTheoryRowReflectionOperator (-1) * oddKTheoryRowZeroProjection) +
        (star (oddKTheoryReflectionCoeffB (oddKTheoryHalfPhase t)) *
          oddKTheoryReflectionCoeffB (oddKTheoryHalfPhase t)) •
            (oddKTheoryRowReflectionOperator (-1) * oddKTheoryRowZeroProjection *
              oddKTheoryRowReflectionOperator (-1))) =
      ∑ i : Fin 4, oddKTheoryLoopDefectScalarEntries i t •
        oddKTheoryRowLoopFixedFiniteOperator (B := B) (E := E) i := by
    simp only [Fin.sum_univ_four, oddKTheoryLoopDefectScalarEntries,
      oddKTheoryLoopProjectionScalarEntries, oddKTheoryRowLoopFixedFiniteOperator,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.tail_cons, Matrix.head_cons, smul_add, smul_smul]
  rw [hexpand] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

end DefectFormula
end BC4lean.KKTheory
