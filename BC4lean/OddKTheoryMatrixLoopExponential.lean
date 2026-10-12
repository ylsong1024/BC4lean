import BC4lean.OddKTheoryMatrixLoopFunctionalCalculus

/-! # Exact finite-entry exponential of the actual odd Fredholm pullback

The endpoint-zero exponential factor simplifies the actual weighted CFC
formula to the four entries of (exp(2πit)-1)Q_t. Only their periodic products
are descended and evaluated. The nonperiodic projection Q_t is not itself
fed to unitary CFC.
-/

noncomputable section
namespace BC4lean.KKTheory

/-- Four interval entries of the actual finite exponential defect. -/
def oddKTheoryLoopExponentialScalarEntry (i : Fin 4) (t : ℝ) : ℂ :=
  oddFredholmExponentialDefect (2 * (t : ℂ) - 1) * oddKTheoryLoopProjectionScalarEntries t i

theorem continuous_oddKTheoryLoopExponentialScalarEntry (i : Fin 4) :
    Continuous (oddKTheoryLoopExponentialScalarEntry i) := by
  fin_cases i
  all_goals
    unfold oddKTheoryLoopExponentialScalarEntry oddKTheoryLoopProjectionScalarEntries
    have hd := oddFredholmExponentialDefect_continuous
    unfold oddKTheoryReflectionCoeffA oddKTheoryReflectionCoeffB
    fun_prop

@[simp] theorem oddKTheoryLoopExponentialScalarEntry_zero (i : Fin 4) :
    oddKTheoryLoopExponentialScalarEntry i 0 = 0 := by
  simp [oddKTheoryLoopExponentialScalarEntry]

@[simp] theorem oddKTheoryLoopExponentialScalarEntry_one (i : Fin 4) :
    oddKTheoryLoopExponentialScalarEntry i 1 = 0 := by
  norm_num [oddKTheoryLoopExponentialScalarEntry]

/-- The exponential phase is exactly the once-around circle coordinate. -/
theorem oddKTheoryLoopExponentialScalarEntry_phase (i : Fin 4) (t : ℝ) :
    oddKTheoryLoopExponentialScalarEntry i t =
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) - 1) *
        oddKTheoryLoopProjectionScalarEntries t i := by
  unfold oddKTheoryLoopExponentialScalarEntry oddFredholmExponentialDefect
  have hphase : Complex.I * (Real.pi : ℂ) * (2 * (t : ℂ) - 1 + 1) =
      2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) := by ring
  rw [hphase]

/-- The actual continuous circle entries of the finite exponential defect. -/
def oddKTheoryLoopExponentialCircleEntry (i : Fin 4) : C(Circle, ℂ) :=
  oddKTheoryDescendScalarLoop (oddKTheoryLoopExponentialScalarEntry i)
    (continuous_oddKTheoryLoopExponentialScalarEntry i) (by simp)

@[simp] theorem oddKTheoryLoopExponentialCircleEntry_one (i : Fin 4) :
    oddKTheoryLoopExponentialCircleEntry i 1 = 0 := by
  simp [oddKTheoryLoopExponentialCircleEntry]

/-- Exact scalar simplification of the continuous endpoint-zero factor. -/
theorem oddKTheoryLoop_factor_mul_defect_entry (i : Fin 4) (t : ℝ) :
    oddFredholmExponentialFactor (2 * (t : ℂ) - 1) * oddKTheoryLoopDefectScalarEntries i t =
      oddKTheoryLoopExponentialScalarEntry i t := by
  have hs : (2 * (t : ℂ) - 1) ^ 2 - 1 = -4 * (t : ℂ) * (1 - (t : ℂ)) := by ring
  rw [oddKTheoryLoopDefectScalarEntries, ← hs, oddKTheoryLoopExponentialScalarEntry,
    oddFredholmExponentialDefect_factor]
  ring

variable {B ι : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [DecidableEq ι]

/-- The actual weighted CFC coefficient is exactly the descended periodic
finite exponential entry, rather than a CFC of a nonperiodic projection. -/
theorem oddKTheoryMatrixLoopExponential_weighted_entry
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) (i : Fin 4) :
    oddKTheoryLoopWeightedCircleEntry (oddKTheoryMatrixLoopCFCDomain u)
      (oddKTheoryMatrixLoopCFCDomain_contains_segment u)
      ⟨fun z => oddFredholmExponentialFactor z,
        oddFredholmExponentialFactor_continuous.comp continuous_subtype_val⟩ i =
      oddKTheoryLoopExponentialCircleEntry i := by
  ext z
  rw [oddKTheoryLoopWeightedCircleEntry_apply]
  simp only [ContinuousMap.coe_mk, oddKTheoryLoopClampedEigenvalue_coe_parameter,
    oddKTheoryLoopDefectCircleEntry, oddKTheoryLoopExponentialCircleEntry,
    oddKTheoryDescendScalarLoop_apply]
  exact oddKTheoryLoop_factor_mul_defect_entry i _

/-- The actual infinite Fredholm exponential has exactly four genuine
matrix-CFC row entries; all coefficient functions vanish at scalar 1. -/
theorem oddKTheoryMatrixLoopPullback_exponential_sub_one
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) :
    (oddFredholmExponential (A := OddKTheoryMatrixRowOperator B ι)
      (oddKTheoryMatrixLoopSelfAdjoint (B := B) (ι := ι) u) : OddKTheoryMatrixRowOperator B ι) - 1 =
      ∑ i : Fin 4, oddKTheoryMatrixCircleCoefficient u (oddKTheoryLoopExponentialCircleEntry i) *
        oddKTheoryRowLoopFixedFiniteOperator i := by
  rw [oddKTheoryMatrixLoopPullback_exponential_sub_one_weighted,
    oddKTheoryMatrixWeightedDefectCLM_apply]
  simp only [oddKTheoryMatrixLoopExponential_weighted_entry]

end BC4lean.KKTheory
