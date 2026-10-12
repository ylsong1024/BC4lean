import BC4lean.OddKTheoryRowUniversalLoop
import BC4lean.OddKTheoryPeriodicExpansion

/-! # Exact periodic expansion on actual countable finite-row modules

The actual row-module universal loop has the same genuine periodic scalar
coefficients, with fixed actual integer-coordinate operators. This is the
finite formula suitable for matrix unitary coefficient functional calculus.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

/-- The actual projection in the square defect has only the zero and minus-one
coordinates. Its entries need not lie in B until scalar coefficient pullback. -/
def oddKTheoryRowTwoCoordinateProjection (t : ℝ) : OddKTheoryCountableOperator B E :=
  star (oddKTheoryRowReflectionPhaseOperator (B := B) (E := E) (-1) t : OddKTheoryCountableOperator B E) *
    oddKTheoryRowZeroProjection *
      (oddKTheoryRowReflectionPhaseOperator (B := B) (E := E) (-1) t : OddKTheoryCountableOperator B E)

theorem oddKTheoryRowLoopConjugator_zeroProjection (t : ℝ) :
    star (oddKTheoryRowLoopConjugator (B := B) (E := E) t : OddKTheoryCountableOperator B E) *
        oddKTheoryRowZeroProjection * (oddKTheoryRowLoopConjugator (B := B) (E := E) t : OddKTheoryCountableOperator B E) =
      oddKTheoryRowTwoCoordinateProjection t := by
  let W₀ := oddKTheoryRowReflectionPhaseOperator (B := B) (E := E) 0 t
  let W₁ := oddKTheoryRowReflectionPhaseOperator (B := B) (E := E) (-1) t
  have hfix : star (W₀ : OddKTheoryCountableOperator B E) * oddKTheoryRowZeroProjection =
      oddKTheoryRowZeroProjection :=
    oddKTheoryReflectionPhaseElement_star_mul_of_fixed _ _
      (oddKTheoryRowReflectionOperator_star 0)
      oddKTheoryRowReflection_zero_mul_zeroProjection _
  have hfix' : oddKTheoryRowZeroProjection * (W₀ : OddKTheoryCountableOperator B E) =
      oddKTheoryRowZeroProjection := by
    have h := congrArg star hfix
    simpa only [star_mul, star_star, oddKTheoryRowZeroProjection_star] using h
  change star ((W₀ : OddKTheoryCountableOperator B E) *
      (W₁ : OddKTheoryCountableOperator B E)) * oddKTheoryRowZeroProjection *
    ((W₀ : OddKTheoryCountableOperator B E) * (W₁ : OddKTheoryCountableOperator B E)) = _
  rw [star_mul]
  calc
    _ = star (W₁ : OddKTheoryCountableOperator B E) *
        (star (W₀ : OddKTheoryCountableOperator B E) * oddKTheoryRowZeroProjection *
          (W₀ : OddKTheoryCountableOperator B E)) * (W₁ : OddKTheoryCountableOperator B E) := by
      simp only [mul_assoc]
    _ = oddKTheoryRowTwoCoordinateProjection t := by rw [hfix, hfix']; rfl

theorem oddKTheoryRowTwoCoordinateProjection_expansion (t : ℝ) :
    oddKTheoryRowTwoCoordinateProjection (B := B) (E := E) t =
      (star (oddKTheoryReflectionCoeffA (oddKTheoryHalfPhase t)) *
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
            oddKTheoryRowReflectionOperator (-1)) :=
  oddKTheoryReflectionPhaseElement_conjugate_expansion _ _
    (oddKTheoryRowReflectionOperator_star (-1)) _

theorem oddKTheoryRowUniversalFredholmLoop_twoCoordinate_square_defect (t : ℝ) :
    oddKTheoryRowUniversalFredholmLoop (B := B) (E := E) t * oddKTheoryRowUniversalFredholmLoop t - 1 =
      (-4 * (t : ℂ) * (1 - (t : ℂ))) • oddKTheoryRowTwoCoordinateProjection t := by
  rw [oddKTheoryRowUniversalFredholmLoop_square_defect,
    oddKTheoryRowLoopConjugator_zeroProjection]

def oddKTheoryRowLoopFixedPermutation : Fin 4 → OddKTheoryCountableOperator B E :=
  ![1, oddKTheoryRowReflectionOperator 0, oddKTheoryRowReflectionOperator (-1),
    oddKTheoryRowReflectionOperator 0 * oddKTheoryRowReflectionOperator (-1)]

def oddKTheoryRowLoopFixedOperator (p : Fin 4 × Fin 4) : OddKTheoryCountableOperator B E :=
  star (oddKTheoryRowLoopFixedPermutation p.1) * oddKTheoryRowSignOperator *
    oddKTheoryRowLoopFixedPermutation p.2

def oddKTheoryRowLoopFixedFiniteOperator : Fin 4 → OddKTheoryCountableOperator B E :=
  ![oddKTheoryRowZeroProjection, oddKTheoryRowZeroProjection * oddKTheoryRowReflectionOperator (-1),
    oddKTheoryRowReflectionOperator (-1) * oddKTheoryRowZeroProjection,
    oddKTheoryRowReflectionOperator (-1) * oddKTheoryRowZeroProjection *
      oddKTheoryRowReflectionOperator (-1)]

/-- The actual conjugator uses exactly four fixed signed permutations. -/
theorem oddKTheoryRowLoopConjugator_finiteExpansion (t : ℝ) :
    (oddKTheoryRowLoopConjugator (B := B) (E := E) t : OddKTheoryCountableOperator B E) =
      ∑ i : Fin 4, oddKTheoryLoopScalarCoefficients t i • oddKTheoryRowLoopFixedPermutation i := by
  let a := oddKTheoryReflectionCoeffA (oddKTheoryHalfPhase t)
  let b := oddKTheoryReflectionCoeffB (oddKTheoryHalfPhase t)
  let R₀ := oddKTheoryRowReflectionOperator (B := B) (E := E) 0
  let R₁ := oddKTheoryRowReflectionOperator (B := B) (E := E) (-1)
  rw [Fin.sum_univ_four]
  change (a • (1 : OddKTheoryCountableOperator B E) + b • R₀) * (a • 1 + b • R₁) =
    (a ^ 2) • 1 + (a * b) • R₀ + (a * b) • R₁ + (b ^ 2) • (R₀ * R₁)
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

omit [CompleteSpace E] in
@[simp] theorem oddKTheoryRowLoopFixedOperator_zero_zero [CompleteSpace E] :
    oddKTheoryRowLoopFixedOperator (B := B) (E := E) (0, 0) = oddKTheoryRowSignOperator := by
  simp [oddKTheoryRowLoopFixedOperator, oddKTheoryRowLoopFixedPermutation]

/-- The other distinguished diagonal term contributes exactly one actual
finite-coordinate correction. -/
theorem oddKTheoryRowLoopFixedOperator_three_three :
    oddKTheoryRowLoopFixedOperator (B := B) (E := E) (3, 3) =
      oddKTheoryRowSignOperator - (2 : ℂ) •
        (oddKTheoryRowReflectionOperator (-1) * oddKTheoryRowZeroProjection *
          oddKTheoryRowReflectionOperator (-1)) := by
  change star (oddKTheoryRowReflectionOperator (B := B) (E := E) 0 *
      oddKTheoryRowReflectionOperator (-1)) * oddKTheoryRowSignOperator *
      (oddKTheoryRowReflectionOperator 0 * oddKTheoryRowReflectionOperator (-1)) = _
  rw [star_mul, oddKTheoryRowReflectionOperator_star, oddKTheoryRowReflectionOperator_star]
  calc
    _ = oddKTheoryRowReflectionOperator (-1) *
        (oddKTheoryRowReflectionOperator 0 * oddKTheoryRowSignOperator *
          oddKTheoryRowReflectionOperator 0) * oddKTheoryRowReflectionOperator (-1) := by
      simp only [mul_assoc]
    _ = _ := by
      rw [oddKTheoryRowReflection_zero_sign_conjugate, mul_sub, sub_mul, mul_neg, neg_mul,
        oddKTheoryRowReflection_neg_one_sign_conjugate, neg_neg,
        mul_smul_comm, smul_mul_assoc]

/-- The complete actual interval loop is already a finite fixed-operator
formula before combining its distinguished diagonal coefficients. -/
theorem oddKTheoryRowUniversalFredholmLoop_rawExpansion (t : ℝ) :
    oddKTheoryRowUniversalFredholmLoop (B := B) (E := E) t =
      (∑ p : Fin 4 × Fin 4,
        oddKTheoryLoopPairCoefficient p t • oddKTheoryRowLoopFixedOperator p) +
      (2 * (t : ℂ)) • oddKTheoryRowTwoCoordinateProjection t := by
  have hV := oddKTheoryRowLoopConjugator_finiteExpansion (B := B) (E := E) t
  calc
    _ = star (oddKTheoryRowLoopConjugator (B := B) (E := E) t : OddKTheoryCountableOperator B E) *
        oddKTheoryRowSignOperator * (oddKTheoryRowLoopConjugator (B := B) (E := E) t : OddKTheoryCountableOperator B E) +
        (2 * (t : ℂ)) • oddKTheoryRowTwoCoordinateProjection t := by
      rw [oddKTheoryRowUniversalFredholmLoop, oddKTheoryRowCrossingOperator,
        mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
        oddKTheoryRowLoopConjugator_zeroProjection]
    _ = _ := by
      congr 1
      simp only [hV, Fintype.sum_prod_type, star_sum, star_smul, Finset.sum_mul, Finset.mul_sum,
        smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul,
        oddKTheoryLoopPairCoefficient, oddKTheoryRowLoopFixedOperator, mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_comm (oddKTheoryLoopScalarCoefficients t j)
        (star (oddKTheoryLoopScalarCoefficients t i))]

/-- Separate the two actual distinguished diagonal terms. The residual
permutation coefficients all descend continuously to the circle. -/
theorem oddKTheoryRowUniversalFredholmLoop_periodicPermutationExpansion (t : ℝ) :
    oddKTheoryRowUniversalFredholmLoop (B := B) (E := E) t =
      (∑ p : Fin 4 × Fin 4,
        oddKTheoryLoopResidualCoefficient p t • oddKTheoryRowLoopFixedOperator p) +
      oddKTheoryLoopSignCoefficient t • oddKTheoryRowSignOperator +
      ((2 * (t : ℂ)) • oddKTheoryRowTwoCoordinateProjection t -
        (2 * oddKTheoryLoopPairCoefficient (3, 3) t) •
          (oddKTheoryRowReflectionOperator (-1) * oddKTheoryRowZeroProjection *
            oddKTheoryRowReflectionOperator (-1))) := by
  have hsplit : (∑ p : Fin 4 × Fin 4,
      oddKTheoryLoopPairCoefficient p t • oddKTheoryRowLoopFixedOperator (B := B) (E := E) p) =
      (∑ p : Fin 4 × Fin 4,
        oddKTheoryLoopResidualCoefficient p t • oddKTheoryRowLoopFixedOperator p) +
        oddKTheoryLoopPairCoefficient (0, 0) t • oddKTheoryRowLoopFixedOperator (0, 0) +
        oddKTheoryLoopPairCoefficient (3, 3) t • oddKTheoryRowLoopFixedOperator (3, 3) := by
    simp only [Fintype.sum_prod_type, Fin.sum_univ_four,
      oddKTheoryLoopResidualCoefficient]
    norm_num [Prod.mk.injEq]
    simp
    abel
  rw [oddKTheoryRowUniversalFredholmLoop_rawExpansion, hsplit,
    oddKTheoryRowLoopFixedOperator_zero_zero, oddKTheoryRowLoopFixedOperator_three_three,
    oddKTheoryLoopSignCoefficient, smul_sub, smul_smul]
  module

/-- The remaining actual two-coordinate correction is a finite formula whose
four scalar coefficients individually match and vanish at the endpoints. -/
theorem oddKTheoryRowLoop_finiteCorrectionExpansion (t : ℝ) :
    (2 * (t : ℂ)) • oddKTheoryRowTwoCoordinateProjection (B := B) (E := E) t -
        (2 * oddKTheoryLoopPairCoefficient (3, 3) t) •
          (oddKTheoryRowReflectionOperator (-1) * oddKTheoryRowZeroProjection *
            oddKTheoryRowReflectionOperator (-1)) =
      ∑ i : Fin 4, oddKTheoryLoopFiniteScalarCoefficients t i •
        oddKTheoryRowLoopFixedFiniteOperator i := by
  let a := oddKTheoryReflectionCoeffA (oddKTheoryHalfPhase t)
  let b := oddKTheoryReflectionCoeffB (oddKTheoryHalfPhase t)
  let P := oddKTheoryRowZeroProjection (B := B) (E := E)
  let R := oddKTheoryRowReflectionOperator (B := B) (E := E) (-1)
  rw [oddKTheoryRowTwoCoordinateProjection_expansion, Fin.sum_univ_four]
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
theorem oddKTheoryRowUniversalFredholmLoop_fullPeriodicExpansion (t : ℝ) :
    oddKTheoryRowUniversalFredholmLoop (B := B) (E := E) t =
      (∑ p : Fin 4 × Fin 4,
        oddKTheoryLoopResidualCoefficient p t • oddKTheoryRowLoopFixedOperator p) +
      oddKTheoryLoopSignCoefficient t • oddKTheoryRowSignOperator +
      ∑ i : Fin 4, oddKTheoryLoopFiniteScalarCoefficients t i •
        oddKTheoryRowLoopFixedFiniteOperator i := by
  rw [oddKTheoryRowUniversalFredholmLoop_periodicPermutationExpansion,
    oddKTheoryRowLoop_finiteCorrectionExpansion]


end BC4lean.KKTheory
