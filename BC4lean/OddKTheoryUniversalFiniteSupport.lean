import BC4lean.OddKTheoryUniversalLoop
import BC4lean.StandardModuleCompactFrame

/-! # The actual two-coordinate defect of the universal odd loop

The first reflection fixes the zero coordinate, so its phase disappears from
the conjugated zero-coordinate projection. The defect is therefore an explicit
sum of four actual coordinate operators. Coordinate operators with coefficients
in B are compact, including for nonunital B; the undecorated coordinate
projection is not asserted compact.
-/

noncomputable section
namespace BC4lean.KKTheory

section ReflectionPhase

variable {A : Type*} [CStarAlgebra A]

theorem oddKTheoryReflectionPhaseElement_mul_of_fixed
    (R P : A) (hRP : R * P = P) (w : unitary ℂ) :
    oddKTheoryReflectionPhaseElement R w * P = P := by
  rw [oddKTheoryReflectionPhaseElement, add_mul, smul_mul_assoc,
    smul_mul_assoc, one_mul, hRP, ← add_smul, oddKTheoryReflectionCoeff_add, one_smul]

theorem oddKTheoryReflectionPhaseElement_star_mul_of_fixed
    (R P : A) (hR : star R = R) (hRP : R * P = P) (w : unitary ℂ) :
    star (oddKTheoryReflectionPhaseElement R w) * P = P := by
  simp only [oddKTheoryReflectionPhaseElement, star_add, star_smul, star_one, hR,
    add_mul, smul_mul_assoc, one_mul, hRP]
  rw [← add_smul, ← star_add, oddKTheoryReflectionCoeff_add, star_one, one_smul]

theorem oddKTheoryReflectionPhaseElement_conjugate_expansion
    (R P : A) (hR : star R = R) (w : unitary ℂ) :
    star (oddKTheoryReflectionPhaseElement R w) * P *
      oddKTheoryReflectionPhaseElement R w =
      (star (oddKTheoryReflectionCoeffA w) * oddKTheoryReflectionCoeffA w) • P +
      (star (oddKTheoryReflectionCoeffA w) * oddKTheoryReflectionCoeffB w) • (P * R) +
      (star (oddKTheoryReflectionCoeffB w) * oddKTheoryReflectionCoeffA w) • (R * P) +
      (star (oddKTheoryReflectionCoeffB w) * oddKTheoryReflectionCoeffB w) • (R * P * R) := by
  simp only [oddKTheoryReflectionPhaseElement, star_add, star_smul, star_one, hR,
    add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

end ReflectionPhase

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The actual projection in the square defect has only the zero and minus-one
coordinates. Its entries need not lie in B until scalar coefficient pullback. -/
def oddKTheoryTwoCoordinateProjection (t : ℝ) : OddKTheoryStandardOperator B :=
  star (oddKTheoryReflectionPhaseOperator (B := B) (-1) t : OddKTheoryStandardOperator B) *
    oddKTheoryZeroProjection *
      (oddKTheoryReflectionPhaseOperator (B := B) (-1) t : OddKTheoryStandardOperator B)

theorem oddKTheoryLoopConjugator_zeroProjection (t : ℝ) :
    star (oddKTheoryLoopConjugator (B := B) t : OddKTheoryStandardOperator B) *
        oddKTheoryZeroProjection * (oddKTheoryLoopConjugator (B := B) t : OddKTheoryStandardOperator B) =
      oddKTheoryTwoCoordinateProjection t := by
  let W₀ := oddKTheoryReflectionPhaseOperator (B := B) 0 t
  let W₁ := oddKTheoryReflectionPhaseOperator (B := B) (-1) t
  have hfix : star (W₀ : OddKTheoryStandardOperator B) * oddKTheoryZeroProjection =
      oddKTheoryZeroProjection :=
    oddKTheoryReflectionPhaseElement_star_mul_of_fixed _ _
      (oddKTheoryReflectionOperator_star 0)
      oddKTheoryReflection_zero_mul_zeroProjection _
  have hfix' : oddKTheoryZeroProjection * (W₀ : OddKTheoryStandardOperator B) =
      oddKTheoryZeroProjection := by
    have h := congrArg star hfix
    simpa only [star_mul, star_star, oddKTheoryZeroProjection_star] using h
  change star ((W₀ : OddKTheoryStandardOperator B) * (W₁ : OddKTheoryStandardOperator B)) *
    oddKTheoryZeroProjection *
    ((W₀ : OddKTheoryStandardOperator B) * (W₁ : OddKTheoryStandardOperator B)) = _
  rw [star_mul]
  calc
    _ = star (W₁ : OddKTheoryStandardOperator B) *
        (star (W₀ : OddKTheoryStandardOperator B) * oddKTheoryZeroProjection *
          (W₀ : OddKTheoryStandardOperator B)) * (W₁ : OddKTheoryStandardOperator B) := by
      simp only [mul_assoc]
    _ = oddKTheoryTwoCoordinateProjection t := by rw [hfix, hfix']; rfl

theorem oddKTheoryTwoCoordinateProjection_expansion (t : ℝ) :
    oddKTheoryTwoCoordinateProjection (B := B) t =
      (star (oddKTheoryReflectionCoeffA (oddKTheoryHalfPhase t)) *
        oddKTheoryReflectionCoeffA (oddKTheoryHalfPhase t)) • oddKTheoryZeroProjection +
      (star (oddKTheoryReflectionCoeffA (oddKTheoryHalfPhase t)) *
        oddKTheoryReflectionCoeffB (oddKTheoryHalfPhase t)) •
          (oddKTheoryZeroProjection * oddKTheoryReflectionOperator (-1)) +
      (star (oddKTheoryReflectionCoeffB (oddKTheoryHalfPhase t)) *
        oddKTheoryReflectionCoeffA (oddKTheoryHalfPhase t)) •
          (oddKTheoryReflectionOperator (-1) * oddKTheoryZeroProjection) +
      (star (oddKTheoryReflectionCoeffB (oddKTheoryHalfPhase t)) *
        oddKTheoryReflectionCoeffB (oddKTheoryHalfPhase t)) •
          (oddKTheoryReflectionOperator (-1) * oddKTheoryZeroProjection *
            oddKTheoryReflectionOperator (-1)) := by
  change star (oddKTheoryReflectionPhaseElement (oddKTheoryReflectionOperator (B := B) (-1))
      (oddKTheoryHalfPhase t)) * oddKTheoryZeroProjection *
    oddKTheoryReflectionPhaseElement (oddKTheoryReflectionOperator (B := B) (-1))
      (oddKTheoryHalfPhase t) = _
  exact oddKTheoryReflectionPhaseElement_conjugate_expansion
    (oddKTheoryReflectionOperator (B := B) (-1)) (oddKTheoryZeroProjection (B := B))
    (oddKTheoryReflectionOperator_star (B := B) (-1)) (oddKTheoryHalfPhase t)

theorem oddKTheoryUniversalFredholmLoop_twoCoordinate_square_defect (t : ℝ) :
    oddKTheoryUniversalFredholmLoop (B := B) t * oddKTheoryUniversalFredholmLoop t - 1 =
      (-4 * (t : ℂ) * (1 - (t : ℂ))) • oddKTheoryTwoCoordinateProjection t := by
  rw [oddKTheoryUniversalFredholmLoop_square_defect,
    oddKTheoryLoopConjugator_zeroProjection]

/-- A genuine coefficient entry between two actual integer coordinates. -/
def oddKTheoryCoordinateCoefficient (z w : ℤ) (b : B) : OddKTheoryStandardOperator B :=
  ((standardCountableInclusion (oddKTheoryIntegerIndex z)).comp (standardLeftMul b)).comp
    (standardCountableEvaluation (oddKTheoryIntegerIndex w))

/-- B-valued entries are compact even though the corresponding identity entry
at a coordinate need not be compact over a nonunital coefficient algebra. -/
theorem oddKTheoryCoordinateCoefficient_isModuleCompact (z w : ℤ) (b : B) :
    IsModuleCompact (oddKTheoryCoordinateCoefficient z w b) := by
  have hCompact : IsModuleCompact (standardLeftMul (B := B) b) :=
    standardLeftMul_mem_moduleCompact b
  exact (hCompact.comp_left
    (standardCountableInclusion (oddKTheoryIntegerIndex z))).comp_right
      (standardCountableEvaluation (oddKTheoryIntegerIndex w))

theorem oddKTheoryCoordinateCoefficient_add (z w : ℤ) (b c : B) :
    oddKTheoryCoordinateCoefficient z w (b + c) =
      oddKTheoryCoordinateCoefficient z w b + oddKTheoryCoordinateCoefficient z w c := by
  ext x
  simp only [oddKTheoryCoordinateCoefficient, AdjointableMap.comp_apply,
    map_add, AdjointableMap.coe_add_apply]

/-- Every finite collection of genuine B-valued coordinate entries gives an
actual compact operator on the completed infinite module. -/
theorem oddKTheoryFiniteCoordinateCoefficients_isModuleCompact
    {ι : Type*} (s : Finset ι) (z w : ι → ℤ) (b : ι → B) :
    IsModuleCompact (∑ i ∈ s, oddKTheoryCoordinateCoefficient (z i) (w i) (b i)) := by
  exact (moduleCompact B (StandardCountableHilbertModule B)
    (StandardCountableHilbertModule B)).sum_mem fun i _ =>
      oddKTheoryCoordinateCoefficient_isModuleCompact (z i) (w i) (b i)

end BC4lean.KKTheory
