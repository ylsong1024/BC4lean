import BC4lean.OddKTheoryUniversalFiniteSupport
import BC4lean.OddKTheoryUnitaryFunctionalCalculus
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fin.VecNotation

/-! # A finite periodic scalar expansion of the actual universal odd loop

Expand the two reflection phases into the four actual fixed permutations
1,R₀,R₁,R₀R₁. Among the sixteen conjugation coefficients only the two extreme
diagonal terms fail endpoint matching separately. Their operator terms are
D and D-2R₁P₀R₁. Combining their D coefficients, and combining the finite
correction with the crossing projection, makes every scalar coefficient
periodic. Thus the actual infinite-module loop is a finite fixed-operator
formula with genuine continuous circle coefficients.
-/

noncomputable section
namespace BC4lean.KKTheory

def oddKTheoryLoopScalarCoefficients (t : ℝ) : Fin 4 → ℂ :=
  let a := oddKTheoryReflectionCoeffA (oddKTheoryHalfPhase t)
  let b := oddKTheoryReflectionCoeffB (oddKTheoryHalfPhase t)
  ![a ^ 2, a * b, a * b, b ^ 2]

theorem continuous_oddKTheoryLoopScalarCoefficients (i : Fin 4) :
    Continuous (fun t => oddKTheoryLoopScalarCoefficients t i) := by
  fin_cases i <;> unfold oddKTheoryLoopScalarCoefficients
  all_goals
    unfold oddKTheoryReflectionCoeffA oddKTheoryReflectionCoeffB
    fun_prop

@[simp] theorem oddKTheoryLoopScalarCoefficients_zero (i : Fin 4) :
    oddKTheoryLoopScalarCoefficients 0 i = if i = 0 then 1 else 0 := by
  fin_cases i <;>
    simp [oddKTheoryLoopScalarCoefficients, oddKTheoryReflectionCoeffA,
      oddKTheoryReflectionCoeffB]

@[simp] theorem oddKTheoryLoopScalarCoefficients_one (i : Fin 4) :
    oddKTheoryLoopScalarCoefficients 1 i = if i = 3 then 1 else 0 := by
  fin_cases i <;>
    simp [oddKTheoryLoopScalarCoefficients, oddKTheoryReflectionCoeffA,
      oddKTheoryReflectionCoeffB]

def oddKTheoryLoopPairCoefficient (p : Fin 4 × Fin 4) (t : ℝ) : ℂ :=
  star (oddKTheoryLoopScalarCoefficients t p.1) * oddKTheoryLoopScalarCoefficients t p.2

/-- The fourteen remaining permutation coefficients, written as a sixteen
term sum with its two distinguished diagonal coefficients zero. -/
def oddKTheoryLoopResidualCoefficient (p : Fin 4 × Fin 4) (t : ℝ) : ℂ :=
  if p = (0, 0) ∨ p = (3, 3) then 0 else oddKTheoryLoopPairCoefficient p t

theorem continuous_oddKTheoryLoopResidualCoefficient (p : Fin 4 × Fin 4) :
    Continuous (oddKTheoryLoopResidualCoefficient p) := by
  unfold oddKTheoryLoopResidualCoefficient
  split_ifs
  · exact continuous_const
  · exact (continuous_oddKTheoryLoopScalarCoefficients p.1).star.mul
      (continuous_oddKTheoryLoopScalarCoefficients p.2)

@[simp] theorem oddKTheoryLoopResidualCoefficient_zero (p : Fin 4 × Fin 4) :
    oddKTheoryLoopResidualCoefficient p 0 = 0 := by
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [oddKTheoryLoopResidualCoefficient, oddKTheoryLoopPairCoefficient]

@[simp] theorem oddKTheoryLoopResidualCoefficient_one (p : Fin 4 × Fin 4) :
    oddKTheoryLoopResidualCoefficient p 1 = 0 := by
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [oddKTheoryLoopResidualCoefficient, oddKTheoryLoopPairCoefficient]

def oddKTheoryLoopSignCoefficient (t : ℝ) : ℂ :=
  oddKTheoryLoopPairCoefficient (0, 0) t + oddKTheoryLoopPairCoefficient (3, 3) t

theorem continuous_oddKTheoryLoopSignCoefficient : Continuous oddKTheoryLoopSignCoefficient :=
  ((continuous_oddKTheoryLoopScalarCoefficients 0).star.mul
    (continuous_oddKTheoryLoopScalarCoefficients 0)).add
    ((continuous_oddKTheoryLoopScalarCoefficients 3).star.mul
      (continuous_oddKTheoryLoopScalarCoefficients 3))

@[simp] theorem oddKTheoryLoopSignCoefficient_zero : oddKTheoryLoopSignCoefficient 0 = 1 := by
  simp [oddKTheoryLoopSignCoefficient, oddKTheoryLoopPairCoefficient]

@[simp] theorem oddKTheoryLoopSignCoefficient_one : oddKTheoryLoopSignCoefficient 1 = 1 := by
  simp [oddKTheoryLoopSignCoefficient, oddKTheoryLoopPairCoefficient]

/-- The genuine continuous circle coefficients for the fixed sign operator. -/
def oddKTheoryLoopSignCircleCoefficient : C(Circle, ℂ) :=
  oddKTheoryDescendScalarLoop oddKTheoryLoopSignCoefficient
    continuous_oddKTheoryLoopSignCoefficient (by simp)

/-- The genuine continuous circle coefficients for the fourteen fixed
permutation terms. Each one vanishes at the circle base point. -/
def oddKTheoryLoopResidualCircleCoefficient (p : Fin 4 × Fin 4) : C(Circle, ℂ) :=
  oddKTheoryDescendScalarLoop (oddKTheoryLoopResidualCoefficient p)
    (continuous_oddKTheoryLoopResidualCoefficient p) (by simp)

@[simp] theorem oddKTheoryLoopSignCircleCoefficient_one :
    oddKTheoryLoopSignCircleCoefficient 1 = 1 := by
  simp [oddKTheoryLoopSignCircleCoefficient]

@[simp] theorem oddKTheoryLoopResidualCircleCoefficient_one (p : Fin 4 × Fin 4) :
    oddKTheoryLoopResidualCircleCoefficient p 1 = 0 := by
  simp [oddKTheoryLoopResidualCircleCoefficient]

/-- Four finite-coordinate correction coefficients after the exceptional
diagonal term is combined with the crossing projection. -/
def oddKTheoryLoopFiniteScalarCoefficients (t : ℝ) : Fin 4 → ℂ :=
  let a := oddKTheoryReflectionCoeffA (oddKTheoryHalfPhase t)
  let b := oddKTheoryReflectionCoeffB (oddKTheoryHalfPhase t)
  ![2 * (t : ℂ) * (star a * a), 2 * (t : ℂ) * (star a * b),
    2 * (t : ℂ) * (star b * a),
    2 * (t : ℂ) * (star b * b) - 2 * (star (b ^ 2) * b ^ 2)]

theorem continuous_oddKTheoryLoopFiniteScalarCoefficients (i : Fin 4) :
    Continuous (fun t => oddKTheoryLoopFiniteScalarCoefficients t i) := by
  fin_cases i <;> unfold oddKTheoryLoopFiniteScalarCoefficients
  all_goals
    unfold oddKTheoryReflectionCoeffA oddKTheoryReflectionCoeffB
    fun_prop

@[simp] theorem oddKTheoryLoopFiniteScalarCoefficients_zero (i : Fin 4) :
    oddKTheoryLoopFiniteScalarCoefficients 0 i = 0 := by
  fin_cases i <;>
    simp [oddKTheoryLoopFiniteScalarCoefficients, oddKTheoryReflectionCoeffA,
      oddKTheoryReflectionCoeffB]

@[simp] theorem oddKTheoryLoopFiniteScalarCoefficients_one (i : Fin 4) :
    oddKTheoryLoopFiniteScalarCoefficients 1 i = 0 := by
  fin_cases i <;>
    simp [oddKTheoryLoopFiniteScalarCoefficients, oddKTheoryReflectionCoeffA,
      oddKTheoryReflectionCoeffB]

/-- Each actual finite-coordinate correction has a continuous circle
coefficient vanishing at the base point. -/
def oddKTheoryLoopFiniteCircleCoefficient (i : Fin 4) : C(Circle, ℂ) :=
  oddKTheoryDescendScalarLoop (fun t => oddKTheoryLoopFiniteScalarCoefficients t i)
    (continuous_oddKTheoryLoopFiniteScalarCoefficients i) (by simp)

@[simp] theorem oddKTheoryLoopFiniteCircleCoefficient_one (i : Fin 4) :
    oddKTheoryLoopFiniteCircleCoefficient i 1 = 0 := by
  simp [oddKTheoryLoopFiniteCircleCoefficient]

theorem oddKTheoryLoopResidualCoefficient_star (p : Fin 4 × Fin 4) (t : ℝ) :
    star (oddKTheoryLoopResidualCoefficient p t) = oddKTheoryLoopResidualCoefficient p.swap t := by
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [oddKTheoryLoopResidualCoefficient, oddKTheoryLoopPairCoefficient, star_mul]

theorem oddKTheoryLoopResidualCircleCoefficient_star (p : Fin 4 × Fin 4) :
    star (oddKTheoryLoopResidualCircleCoefficient p) = oddKTheoryLoopResidualCircleCoefficient p.swap := by
  ext z
  simp only [ContinuousMap.star_apply, oddKTheoryLoopResidualCircleCoefficient,
    oddKTheoryDescendScalarLoop_apply, oddKTheoryLoopResidualCoefficient_star]

theorem oddKTheoryLoopSignCircleCoefficient_star :
    star oddKTheoryLoopSignCircleCoefficient = oddKTheoryLoopSignCircleCoefficient := by
  ext z
  simp only [ContinuousMap.star_apply, oddKTheoryLoopSignCircleCoefficient,
    oddKTheoryDescendScalarLoop_apply, oddKTheoryLoopSignCoefficient,
    oddKTheoryLoopPairCoefficient, star_add, star_mul, star_star]

/-- Adjoints interchange the two off-diagonal finite entries. -/
def oddKTheoryFiniteEntryAdjoint : Fin 4 ≃ Fin 4 := Equiv.swap 1 2

theorem oddKTheoryLoopFiniteScalarCoefficients_star (i : Fin 4) (t : ℝ) :
    star (oddKTheoryLoopFiniteScalarCoefficients t i) =
      oddKTheoryLoopFiniteScalarCoefficients t (oddKTheoryFiniteEntryAdjoint i) := by
  let a := oddKTheoryReflectionCoeffA (oddKTheoryHalfPhase t)
  let b := oddKTheoryReflectionCoeffB (oddKTheoryHalfPhase t)
  have ht : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
  fin_cases i
  · change star (2 * (t : ℂ) * (star a * a)) = 2 * (t : ℂ) * (star a * a)
    simp only [star_mul, star_star, star_ofNat, ht]
    ring
  · change star (2 * (t : ℂ) * (star a * b)) = 2 * (t : ℂ) * (star b * a)
    simp only [star_mul, star_star, star_ofNat, ht]
    ring
  · change star (2 * (t : ℂ) * (star b * a)) = 2 * (t : ℂ) * (star a * b)
    simp only [star_mul, star_star, star_ofNat, ht]
    ring
  · change star (2 * (t : ℂ) * (star b * b) - 2 * (star (b ^ 2) * b ^ 2)) =
      2 * (t : ℂ) * (star b * b) - 2 * (star (b ^ 2) * b ^ 2)
    simp only [star_sub, star_mul, star_star, star_ofNat, ht]
    ring

theorem oddKTheoryLoopFiniteCircleCoefficient_star (i : Fin 4) :
    star (oddKTheoryLoopFiniteCircleCoefficient i) =
      oddKTheoryLoopFiniteCircleCoefficient (oddKTheoryFiniteEntryAdjoint i) := by
  ext z
  simp only [ContinuousMap.star_apply, oddKTheoryLoopFiniteCircleCoefficient,
    oddKTheoryDescendScalarLoop_apply, oddKTheoryLoopFiniteScalarCoefficients_star]

section ActualOperators

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def oddKTheoryLoopFixedPermutation : Fin 4 → OddKTheoryStandardOperator B :=
  ![1, oddKTheoryReflectionOperator 0, oddKTheoryReflectionOperator (-1),
    oddKTheoryReflectionOperator 0 * oddKTheoryReflectionOperator (-1)]

def oddKTheoryLoopFixedOperator (p : Fin 4 × Fin 4) : OddKTheoryStandardOperator B :=
  star (oddKTheoryLoopFixedPermutation p.1) * oddKTheorySignOperator *
    oddKTheoryLoopFixedPermutation p.2

def oddKTheoryLoopFixedFiniteOperator : Fin 4 → OddKTheoryStandardOperator B :=
  ![oddKTheoryZeroProjection, oddKTheoryZeroProjection * oddKTheoryReflectionOperator (-1),
    oddKTheoryReflectionOperator (-1) * oddKTheoryZeroProjection,
    oddKTheoryReflectionOperator (-1) * oddKTheoryZeroProjection *
      oddKTheoryReflectionOperator (-1)]

/-- The actual conjugator uses exactly four fixed signed permutations. -/
theorem oddKTheoryLoopConjugator_finiteExpansion (t : ℝ) :
    (oddKTheoryLoopConjugator (B := B) t : OddKTheoryStandardOperator B) =
      ∑ i : Fin 4, oddKTheoryLoopScalarCoefficients t i • oddKTheoryLoopFixedPermutation i := by
  let a := oddKTheoryReflectionCoeffA (oddKTheoryHalfPhase t)
  let b := oddKTheoryReflectionCoeffB (oddKTheoryHalfPhase t)
  let R₀ := oddKTheoryReflectionOperator (B := B) 0
  let R₁ := oddKTheoryReflectionOperator (B := B) (-1)
  rw [Fin.sum_univ_four]
  change (a • (1 : OddKTheoryStandardOperator B) + b • R₀) * (a • 1 + b • R₁) =
    (a ^ 2) • 1 + (a * b) • R₀ + (a * b) • R₁ + (b ^ 2) • (R₀ * R₁)
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

@[simp] theorem oddKTheoryLoopFixedOperator_zero_zero :
    oddKTheoryLoopFixedOperator (B := B) (0, 0) = oddKTheorySignOperator := by
  simp [oddKTheoryLoopFixedOperator, oddKTheoryLoopFixedPermutation]

/-- The other distinguished diagonal term contributes exactly one actual
finite-coordinate correction. -/
theorem oddKTheoryLoopFixedOperator_three_three :
    oddKTheoryLoopFixedOperator (B := B) (3, 3) =
      oddKTheorySignOperator - (2 : ℂ) •
        (oddKTheoryReflectionOperator (-1) * oddKTheoryZeroProjection *
          oddKTheoryReflectionOperator (-1)) := by
  change star (oddKTheoryReflectionOperator (B := B) 0 *
      oddKTheoryReflectionOperator (-1)) * oddKTheorySignOperator *
      (oddKTheoryReflectionOperator 0 * oddKTheoryReflectionOperator (-1)) = _
  rw [star_mul, oddKTheoryReflectionOperator_star, oddKTheoryReflectionOperator_star]
  calc
    _ = oddKTheoryReflectionOperator (-1) *
        (oddKTheoryReflectionOperator 0 * oddKTheorySignOperator *
          oddKTheoryReflectionOperator 0) * oddKTheoryReflectionOperator (-1) := by
      simp only [mul_assoc]
    _ = _ := by
      rw [oddKTheoryReflection_zero_sign_conjugate, mul_sub, sub_mul, mul_neg, neg_mul,
        oddKTheoryReflection_neg_one_sign_conjugate, neg_neg,
        mul_smul_comm, smul_mul_assoc]

/-- The complete actual interval loop is already a finite fixed-operator
formula before combining its distinguished diagonal coefficients. -/
theorem oddKTheoryUniversalFredholmLoop_rawExpansion (t : ℝ) :
    oddKTheoryUniversalFredholmLoop (B := B) t =
      (∑ p : Fin 4 × Fin 4,
        oddKTheoryLoopPairCoefficient p t • oddKTheoryLoopFixedOperator p) +
      (2 * (t : ℂ)) • oddKTheoryTwoCoordinateProjection t := by
  have hV := oddKTheoryLoopConjugator_finiteExpansion (B := B) t
  calc
    _ = star (oddKTheoryLoopConjugator (B := B) t : OddKTheoryStandardOperator B) *
        oddKTheorySignOperator *
          (oddKTheoryLoopConjugator (B := B) t : OddKTheoryStandardOperator B) +
        (2 * (t : ℂ)) • oddKTheoryTwoCoordinateProjection t := by
      rw [oddKTheoryUniversalFredholmLoop, oddKTheoryCrossingOperator,
        mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
        oddKTheoryLoopConjugator_zeroProjection]
    _ = _ := by
      congr 1
      simp only [hV, Fintype.sum_prod_type, star_sum, star_smul, Finset.sum_mul, Finset.mul_sum,
        smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul,
        oddKTheoryLoopPairCoefficient, oddKTheoryLoopFixedOperator, mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_comm (oddKTheoryLoopScalarCoefficients t j)
        (star (oddKTheoryLoopScalarCoefficients t i))]

/-- Separate the two actual distinguished diagonal terms. The residual
permutation coefficients all descend continuously to the circle. -/
theorem oddKTheoryUniversalFredholmLoop_periodicPermutationExpansion (t : ℝ) :
    oddKTheoryUniversalFredholmLoop (B := B) t =
      (∑ p : Fin 4 × Fin 4,
        oddKTheoryLoopResidualCoefficient p t • oddKTheoryLoopFixedOperator p) +
      oddKTheoryLoopSignCoefficient t • oddKTheorySignOperator +
      ((2 * (t : ℂ)) • oddKTheoryTwoCoordinateProjection t -
        (2 * oddKTheoryLoopPairCoefficient (3, 3) t) •
          (oddKTheoryReflectionOperator (-1) * oddKTheoryZeroProjection *
            oddKTheoryReflectionOperator (-1))) := by
  have hsplit : (∑ p : Fin 4 × Fin 4,
      oddKTheoryLoopPairCoefficient p t • oddKTheoryLoopFixedOperator (B := B) p) =
      (∑ p : Fin 4 × Fin 4,
        oddKTheoryLoopResidualCoefficient p t • oddKTheoryLoopFixedOperator p) +
        oddKTheoryLoopPairCoefficient (0, 0) t • oddKTheoryLoopFixedOperator (0, 0) +
        oddKTheoryLoopPairCoefficient (3, 3) t • oddKTheoryLoopFixedOperator (3, 3) := by
    simp only [Fintype.sum_prod_type, Fin.sum_univ_four,
      oddKTheoryLoopResidualCoefficient]
    norm_num [Prod.mk.injEq]
    simp
    abel
  rw [oddKTheoryUniversalFredholmLoop_rawExpansion, hsplit,
    oddKTheoryLoopFixedOperator_zero_zero, oddKTheoryLoopFixedOperator_three_three,
    oddKTheoryLoopSignCoefficient, smul_sub, smul_smul]
  module

/-- The remaining actual two-coordinate correction is a finite formula whose
four scalar coefficients individually match and vanish at the endpoints. -/
theorem oddKTheoryLoop_finiteCorrectionExpansion (t : ℝ) :
    (2 * (t : ℂ)) • oddKTheoryTwoCoordinateProjection (B := B) t -
        (2 * oddKTheoryLoopPairCoefficient (3, 3) t) •
          (oddKTheoryReflectionOperator (-1) * oddKTheoryZeroProjection *
            oddKTheoryReflectionOperator (-1)) =
      ∑ i : Fin 4, oddKTheoryLoopFiniteScalarCoefficients t i •
        oddKTheoryLoopFixedFiniteOperator i := by
  let a := oddKTheoryReflectionCoeffA (oddKTheoryHalfPhase t)
  let b := oddKTheoryReflectionCoeffB (oddKTheoryHalfPhase t)
  let P := oddKTheoryZeroProjection (B := B)
  let R := oddKTheoryReflectionOperator (B := B) (-1)
  rw [oddKTheoryTwoCoordinateProjection_expansion, Fin.sum_univ_four]
  change (2 * (t : ℂ)) •
      ((star a * a) • P + (star a * b) • (P * R) +
        (star b * a) • (R * P) + (star b * b) • (R * P * R)) -
      (2 * (star (b ^ 2) * b ^ 2)) • (R * P * R) =
    (2 * (t : ℂ) * (star a * a)) • P +
      (2 * (t : ℂ) * (star a * b)) • (P * R) +
      (2 * (t : ℂ) * (star b * a)) • (R * P) +
      (2 * (t : ℂ) * (star b * b) - 2 * (star (b ^ 2) * b ^ 2)) • (R * P * R)
  module

/-- A complete exact finite formula for the genuine infinite-module loop,
with every scalar coefficient individually descending continuously to Circle. -/
theorem oddKTheoryUniversalFredholmLoop_fullPeriodicExpansion (t : ℝ) :
    oddKTheoryUniversalFredholmLoop (B := B) t =
      (∑ p : Fin 4 × Fin 4,
        oddKTheoryLoopResidualCoefficient p t • oddKTheoryLoopFixedOperator p) +
      oddKTheoryLoopSignCoefficient t • oddKTheorySignOperator +
      ∑ i : Fin 4, oddKTheoryLoopFiniteScalarCoefficients t i •
        oddKTheoryLoopFixedFiniteOperator i := by
  rw [oddKTheoryUniversalFredholmLoop_periodicPermutationExpansion,
    oddKTheoryLoop_finiteCorrectionExpansion]

omit [PartialOrder B] [StarOrderedRing B] in
/-- The four periodic finite-entry coefficients evaluate to actual elements
of B when the coefficient unitary has full scalar quotient one. -/
theorem oddKTheoryLoopFiniteCircleCFC_eq_coefficient
    (u : unitary (Unitization ℂ B)) (hu : (u : Unitization ℂ B).fst = 1) (i : Fin 4) :
    oddKTheoryCircleCFC u (oddKTheoryLoopFiniteCircleCoefficient i) =
      (oddKTheoryCircleCFCCoefficient (B := B) u (oddKTheoryLoopFiniteCircleCoefficient i) :
        Unitization ℂ B) :=
  oddKTheoryCircleCFC_eq_coefficient (B := B) u hu _
    (oddKTheoryLoopFiniteCircleCoefficient_one i)

/-- The four resulting genuine coefficient entries give an actual compact
two-coordinate operator on the completed standard module. -/
theorem oddKTheoryLoopFiniteCircleCoefficientEntries_isModuleCompact
    (u : unitary (Unitization ℂ B)) :
    IsModuleCompact (∑ i : Fin 4,
      oddKTheoryCoordinateCoefficient (![0, 0, -1, -1] i) (![0, -1, 0, -1] i)
        (oddKTheoryCircleCFCCoefficient u (oddKTheoryLoopFiniteCircleCoefficient i))) :=
  oddKTheoryFiniteCoordinateCoefficients_isModuleCompact Finset.univ _ _ _

end ActualOperators
end BC4lean.KKTheory
