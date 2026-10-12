import BC4lean.OddKTheoryRowSignedCoordinates
import BC4lean.OddKTheoryUniversalLoop

/-! # The actual universal odd loop on genuine countable row sums

The two-reflection construction acts on the completion of countably many
actual coefficient row modules. In particular the rows can be B^n. All
continuity, selfadjointness, endpoint and exact square-defect identities are
proved for the actual completed B-module operators.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

/-- Actual reflection phase on the genuine infinite coefficient module. -/
def oddKTheoryRowReflectionPhaseOperator (k : ℤ) (t : ℝ) : unitary (OddKTheoryCountableOperator B E) :=
  oddKTheoryReflectionPhase (oddKTheoryRowReflectionOperator k)
    (oddKTheoryRowReflectionOperator_star k) (oddKTheoryRowReflectionOperator_square k)
    (oddKTheoryHalfPhase t)

theorem continuous_oddKTheoryRowReflectionPhaseOperator (k : ℤ) :
    Continuous (oddKTheoryRowReflectionPhaseOperator (B := B) (E := E) k) :=
  ((continuous_oddKTheoryReflectionPhaseElement (oddKTheoryRowReflectionOperator k)).comp
    continuous_oddKTheoryHalfPhase).subtype_mk _

@[simp] theorem oddKTheoryRowReflectionPhaseOperator_zero (k : ℤ) :
    oddKTheoryRowReflectionPhaseOperator (B := B) (E := E) k 0 = 1 := by
  apply Subtype.ext
  simp [oddKTheoryRowReflectionPhaseOperator, oddKTheoryReflectionPhase]

@[simp] theorem oddKTheoryRowReflectionPhaseOperator_one_coe (k : ℤ) :
    (oddKTheoryRowReflectionPhaseOperator (B := B) (E := E) k 1 : OddKTheoryCountableOperator B E) =
      oddKTheoryRowReflectionOperator k :=
  oddKTheoryReflectionPhaseElement_neg_one _ _ oddKTheoryHalfPhase_one_coe

def oddKTheoryRowLoopConjugator (t : ℝ) : unitary (OddKTheoryCountableOperator B E) :=
  oddKTheoryRowReflectionPhaseOperator 0 t * oddKTheoryRowReflectionPhaseOperator (-1) t

theorem continuous_oddKTheoryRowLoopConjugator :
    Continuous (oddKTheoryRowLoopConjugator (B := B) (E := E)) :=
  (continuous_oddKTheoryRowReflectionPhaseOperator 0).mul
    (continuous_oddKTheoryRowReflectionPhaseOperator (-1))

/-- Move just the actual zero coefficient coordinate from -1 to +1. -/
def oddKTheoryRowCrossingOperator (t : ℝ) : OddKTheoryCountableOperator B E :=
  oddKTheoryRowSignOperator + (2 * (t : ℂ)) • oddKTheoryRowZeroProjection

theorem oddKTheoryRowCrossingOperator_star (t : ℝ) :
    star (oddKTheoryRowCrossingOperator (B := B) (E := E) t) = oddKTheoryRowCrossingOperator t := by
  simp only [oddKTheoryRowCrossingOperator, star_add, star_smul,
    oddKTheoryRowSignOperator_star, oddKTheoryRowZeroProjection_star,
    star_mul, star_ofNat, Complex.star_def, Complex.conj_ofReal]
  rw [mul_comm (t : ℂ) 2]

theorem oddKTheoryRowCrossingOperator_square (t : ℝ) :
    oddKTheoryRowCrossingOperator (B := B) (E := E) t * oddKTheoryRowCrossingOperator t =
      1 + (-4 * (t : ℂ) * (1 - (t : ℂ))) • oddKTheoryRowZeroProjection := by
  simp only [oddKTheoryRowCrossingOperator, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, oddKTheoryRowSignOperator_square,
    oddKTheoryRowSign_mul_zeroProjection, oddKTheoryRowZeroProjection_mul_sign,
    oddKTheoryRowZeroProjection_square]
  module

/-- An actual norm-continuous selfadjoint infinite-module loop. -/
def oddKTheoryRowUniversalFredholmLoop (t : ℝ) : OddKTheoryCountableOperator B E :=
  star (oddKTheoryRowLoopConjugator (B := B) (E := E) t : OddKTheoryCountableOperator B E) *
    oddKTheoryRowCrossingOperator t * (oddKTheoryRowLoopConjugator (B := B) (E := E) t : OddKTheoryCountableOperator B E)

theorem continuous_oddKTheoryRowUniversalFredholmLoop :
    Continuous (oddKTheoryRowUniversalFredholmLoop (B := B) (E := E)) := by
  unfold oddKTheoryRowUniversalFredholmLoop oddKTheoryRowCrossingOperator
  have hV : Continuous (fun t => (oddKTheoryRowLoopConjugator (B := B) (E := E) t : OddKTheoryCountableOperator B E)) :=
    continuous_subtype_val.comp continuous_oddKTheoryRowLoopConjugator
  exact (hV.star.mul (by fun_prop)).mul hV

theorem oddKTheoryRowUniversalFredholmLoop_isSelfAdjoint (t : ℝ) :
    IsSelfAdjoint (oddKTheoryRowUniversalFredholmLoop (B := B) (E := E) t) := by
  change star (oddKTheoryRowUniversalFredholmLoop (B := B) (E := E) t) = _
  simp only [oddKTheoryRowUniversalFredholmLoop, star_mul, star_star,
    oddKTheoryRowCrossingOperator_star, mul_assoc]

@[simp] theorem oddKTheoryRowUniversalFredholmLoop_zero :
    oddKTheoryRowUniversalFredholmLoop (B := B) (E := E) 0 = oddKTheoryRowSignOperator := by
  simp [oddKTheoryRowUniversalFredholmLoop, oddKTheoryRowLoopConjugator, oddKTheoryRowCrossingOperator]

/-- The two actual integer reflections make the upper endpoint the same sign
operator. This is an operator identity on the genuine completed module. -/
@[simp] theorem oddKTheoryRowUniversalFredholmLoop_one :
    oddKTheoryRowUniversalFredholmLoop (B := B) (E := E) 1 = oddKTheoryRowSignOperator := by
  simp only [oddKTheoryRowUniversalFredholmLoop, oddKTheoryRowLoopConjugator, Submonoid.coe_mul,
    oddKTheoryRowReflectionPhaseOperator_one_coe, star_mul, oddKTheoryRowReflectionOperator_star,
    oddKTheoryRowCrossingOperator, Complex.ofReal_one, mul_one]
  have hzero : oddKTheoryRowReflectionOperator (B := B) (E := E) 0 *
      (oddKTheoryRowSignOperator + (2 : ℂ) • oddKTheoryRowZeroProjection) *
      oddKTheoryRowReflectionOperator 0 = -oddKTheoryRowSignOperator := by
    rw [mul_add, add_mul, oddKTheoryRowReflection_zero_sign_conjugate,
      mul_smul_comm, oddKTheoryRowReflection_zero_mul_zeroProjection, smul_mul_assoc,
      oddKTheoryRowZeroProjection_mul_reflection_zero]
    module
  calc
    _ = oddKTheoryRowReflectionOperator (-1) *
        (oddKTheoryRowReflectionOperator 0 *
          (oddKTheoryRowSignOperator + (2 : ℂ) • oddKTheoryRowZeroProjection) *
          oddKTheoryRowReflectionOperator 0) * oddKTheoryRowReflectionOperator (-1) := by
      simp only [mul_assoc]
    _ = oddKTheoryRowSignOperator := by
      rw [hzero, mul_neg, neg_mul, oddKTheoryRowReflection_neg_one_sign_conjugate, neg_neg]

/-- The exact square defect of the actual loop. No compactness of the zero
coordinate projection is asserted by this identity. -/
theorem oddKTheoryRowUniversalFredholmLoop_square_defect (t : ℝ) :
    oddKTheoryRowUniversalFredholmLoop (B := B) (E := E) t * oddKTheoryRowUniversalFredholmLoop t - 1 =
      (-4 * (t : ℂ) * (1 - (t : ℂ))) •
        (star (oddKTheoryRowLoopConjugator (B := B) (E := E) t : OddKTheoryCountableOperator B E) *
          oddKTheoryRowZeroProjection * (oddKTheoryRowLoopConjugator (B := B) (E := E) t : OddKTheoryCountableOperator B E)) := by
  let V := oddKTheoryRowLoopConjugator (B := B) (E := E) t
  let T := oddKTheoryRowCrossingOperator (B := B) (E := E) t
  have hVV : (V : OddKTheoryCountableOperator B E) * star (V : OddKTheoryCountableOperator B E) = 1 :=
    Unitary.coe_mul_star_self V
  have hVV' : star (V : OddKTheoryCountableOperator B E) * (V : OddKTheoryCountableOperator B E) = 1 :=
    Unitary.coe_star_mul_self V
  change (star (V : OddKTheoryCountableOperator B E) * T * (V : OddKTheoryCountableOperator B E)) * (star (V : OddKTheoryCountableOperator B E) * T * (V : OddKTheoryCountableOperator B E)) - 1 = _
  calc
    _ = star (V : OddKTheoryCountableOperator B E) * T *
        ((V : OddKTheoryCountableOperator B E) * star (V : OddKTheoryCountableOperator B E)) * T * (V : OddKTheoryCountableOperator B E) - 1 := by
      simp only [mul_assoc]
    _ = star (V : OddKTheoryCountableOperator B E) * (T * T - 1) * (V : OddKTheoryCountableOperator B E) := by
      rw [hVV, mul_one, mul_sub, sub_mul, mul_one, hVV']
      simp only [mul_assoc]
    _ = (-4 * (t : ℂ) * (1 - (t : ℂ))) •
        (star (V : OddKTheoryCountableOperator B E) * oddKTheoryRowZeroProjection * (V : OddKTheoryCountableOperator B E)) := by
      rw [oddKTheoryRowCrossingOperator_square, add_sub_cancel_left,
        mul_smul_comm, smul_mul_assoc]


end BC4lean.KKTheory
