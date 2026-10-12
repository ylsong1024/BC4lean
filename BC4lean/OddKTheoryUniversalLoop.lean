import BC4lean.OddKTheorySignedCoordinates
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # An actual infinite-module selfadjoint loop for the odd inverse

On the genuine standard module let D be the integer sign symmetry, P the
zero-coordinate projection, and R₀,R₁ the actual reflections at 0 and -1/2.
For w=exp(iπt), set Wⱼ=(1+w)/2+(1-w)Rⱼ/2 and V=W₀W₁.
The actual selfadjoint loop is V* (D+2tP) V. Its endpoints are D and its square
defect is -4t(1-t) W₁*PW₁, an actual two-coordinate expression.

This interval construction does not assert P compact over nonunital B. The
scalar coefficient vanishes at both endpoints; pulling the periodic finite
formula back through a scalar-one coefficient unitary is a further step.
-/

noncomputable section
namespace BC4lean.KKTheory

section ReflectionPhase

variable {A : Type*} [CStarAlgebra A]

def oddKTheoryReflectionCoeffA (w : unitary ℂ) : ℂ := (1 + (w : ℂ)) / 2
def oddKTheoryReflectionCoeffB (w : unitary ℂ) : ℂ := (1 - (w : ℂ)) / 2

theorem oddKTheoryReflectionCoeff_add (w : unitary ℂ) :
    oddKTheoryReflectionCoeffA w + oddKTheoryReflectionCoeffB w = 1 := by
  dsimp [oddKTheoryReflectionCoeffA, oddKTheoryReflectionCoeffB]
  ring

theorem oddKTheoryReflectionCoeff_square (w : unitary ℂ) :
    star (oddKTheoryReflectionCoeffA w) * oddKTheoryReflectionCoeffA w +
      star (oddKTheoryReflectionCoeffB w) * oddKTheoryReflectionCoeffB w = 1 := by
  calc
    _ = (1 + star (w : ℂ) * (w : ℂ)) / 2 := by
      simp only [oddKTheoryReflectionCoeffA, oddKTheoryReflectionCoeffB,
        star_div₀, star_add, star_sub, star_one, star_ofNat]
      ring
    _ = 1 := by rw [Unitary.coe_star_mul_self]; norm_num

theorem oddKTheoryReflectionCoeff_cross (w : unitary ℂ) :
    star (oddKTheoryReflectionCoeffA w) * oddKTheoryReflectionCoeffB w +
      star (oddKTheoryReflectionCoeffB w) * oddKTheoryReflectionCoeffA w = 0 := by
  calc
    _ = (1 - star (w : ℂ) * (w : ℂ)) / 2 := by
      simp only [oddKTheoryReflectionCoeffA, oddKTheoryReflectionCoeffB,
        star_div₀, star_add, star_sub, star_one, star_ofNat]
      ring
    _ = 0 := by rw [Unitary.coe_star_mul_self]; norm_num

/-- A finite formula for the actual reflection phase; the phase parameter is
an actual scalar unitary and the reflection is an actual symmetry. -/
def oddKTheoryReflectionPhaseElement (R : A) (w : unitary ℂ) : A :=
  oddKTheoryReflectionCoeffA w • 1 + oddKTheoryReflectionCoeffB w • R

theorem oddKTheoryReflectionPhaseElement_mem_unitary
    (R : A) (hRstar : star R = R) (hRsq : R * R = 1) (w : unitary ℂ) :
    oddKTheoryReflectionPhaseElement R w ∈ unitary A := by
  apply Unitary.mem_iff.mpr
  constructor
  · calc
      star (oddKTheoryReflectionPhaseElement R w) * oddKTheoryReflectionPhaseElement R w =
          (star (oddKTheoryReflectionCoeffA w) * oddKTheoryReflectionCoeffA w +
            star (oddKTheoryReflectionCoeffB w) * oddKTheoryReflectionCoeffB w) • (1 : A) +
          (star (oddKTheoryReflectionCoeffA w) * oddKTheoryReflectionCoeffB w +
            star (oddKTheoryReflectionCoeffB w) * oddKTheoryReflectionCoeffA w) • R := by
        simp only [oddKTheoryReflectionPhaseElement, star_add, star_smul, star_one,
          hRstar, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
          one_mul, mul_one, hRsq]
        module
      _ = 1 := by rw [oddKTheoryReflectionCoeff_square, oddKTheoryReflectionCoeff_cross]; simp
  · calc
      oddKTheoryReflectionPhaseElement R w * star (oddKTheoryReflectionPhaseElement R w) =
          (star (oddKTheoryReflectionCoeffA w) * oddKTheoryReflectionCoeffA w +
            star (oddKTheoryReflectionCoeffB w) * oddKTheoryReflectionCoeffB w) • (1 : A) +
          (star (oddKTheoryReflectionCoeffA w) * oddKTheoryReflectionCoeffB w +
            star (oddKTheoryReflectionCoeffB w) * oddKTheoryReflectionCoeffA w) • R := by
        simp only [oddKTheoryReflectionPhaseElement, star_add, star_smul, star_one,
          hRstar, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
          one_mul, mul_one, hRsq]
        module
      _ = 1 := by rw [oddKTheoryReflectionCoeff_square, oddKTheoryReflectionCoeff_cross]; simp

def oddKTheoryReflectionPhase (R : A) (hRstar : star R = R) (hRsq : R * R = 1)
    (w : unitary ℂ) : unitary A :=
  ⟨oddKTheoryReflectionPhaseElement R w,
    oddKTheoryReflectionPhaseElement_mem_unitary R hRstar hRsq w⟩

theorem continuous_oddKTheoryReflectionPhaseElement (R : A) :
    Continuous (oddKTheoryReflectionPhaseElement R) := by
  have hA : Continuous oddKTheoryReflectionCoeffA := by
    unfold oddKTheoryReflectionCoeffA
    fun_prop
  have hB : Continuous oddKTheoryReflectionCoeffB := by
    unfold oddKTheoryReflectionCoeffB
    fun_prop
  exact (hA.smul continuous_const).add (hB.smul continuous_const)

@[simp] theorem oddKTheoryReflectionPhaseElement_one (R : A) :
    oddKTheoryReflectionPhaseElement R 1 = 1 := by
  simp [oddKTheoryReflectionPhaseElement, oddKTheoryReflectionCoeffA, oddKTheoryReflectionCoeffB]

theorem oddKTheoryReflectionPhaseElement_neg_one (R : A) (w : unitary ℂ)
    (hw : (w : ℂ) = -1) : oddKTheoryReflectionPhaseElement R w = R := by
  simp [oddKTheoryReflectionPhaseElement, oddKTheoryReflectionCoeffA, oddKTheoryReflectionCoeffB, hw]

end ReflectionPhase

/-- The actual scalar unitary w(t)=exp(iπt). -/
def oddKTheoryHalfPhase (t : ℝ) : unitary ℂ :=
  selfAdjoint.expUnitary ((Real.pi * t) • (1 : selfAdjoint ℂ))

@[fun_prop] theorem continuous_oddKTheoryHalfPhase : Continuous oddKTheoryHalfPhase :=
  selfAdjoint.continuous_expUnitary.comp (by fun_prop)

@[simp] theorem oddKTheoryHalfPhase_zero : oddKTheoryHalfPhase 0 = 1 := by
  simp [oddKTheoryHalfPhase]

@[simp] theorem oddKTheoryHalfPhase_one_coe : (oddKTheoryHalfPhase 1 : ℂ) = -1 := by
  change NormedSpace.exp (Complex.I • ((Real.pi * 1) • (1 : ℂ))) = -1
  rw [← Complex.exp_eq_exp_ℂ]
  have harg : Complex.I • ((Real.pi * 1) • (1 : ℂ)) =
      (Real.pi : ℂ) * Complex.I := by
    simp only [mul_one, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
    exact mul_comm _ _
  rw [harg]
  change Complex.exp ((Real.pi : ℂ) * Complex.I) = -(1 : ℂ)
  exact Complex.exp_pi_mul_I

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Actual reflection phase on the genuine infinite coefficient module. -/
def oddKTheoryReflectionPhaseOperator (k : ℤ) (t : ℝ) : unitary (OddKTheoryStandardOperator B) :=
  oddKTheoryReflectionPhase (oddKTheoryReflectionOperator k)
    (oddKTheoryReflectionOperator_star k) (oddKTheoryReflectionOperator_square k)
    (oddKTheoryHalfPhase t)

theorem continuous_oddKTheoryReflectionPhaseOperator (k : ℤ) :
    Continuous (oddKTheoryReflectionPhaseOperator (B := B) k) :=
  ((continuous_oddKTheoryReflectionPhaseElement (oddKTheoryReflectionOperator k)).comp
    continuous_oddKTheoryHalfPhase).subtype_mk _

@[simp] theorem oddKTheoryReflectionPhaseOperator_zero (k : ℤ) :
    oddKTheoryReflectionPhaseOperator (B := B) k 0 = 1 := by
  apply Subtype.ext
  simp [oddKTheoryReflectionPhaseOperator, oddKTheoryReflectionPhase]

@[simp] theorem oddKTheoryReflectionPhaseOperator_one_coe (k : ℤ) :
    (oddKTheoryReflectionPhaseOperator (B := B) k 1 : OddKTheoryStandardOperator B) =
      oddKTheoryReflectionOperator k :=
  oddKTheoryReflectionPhaseElement_neg_one _ _ oddKTheoryHalfPhase_one_coe

def oddKTheoryLoopConjugator (t : ℝ) : unitary (OddKTheoryStandardOperator B) :=
  oddKTheoryReflectionPhaseOperator 0 t * oddKTheoryReflectionPhaseOperator (-1) t

theorem continuous_oddKTheoryLoopConjugator :
    Continuous (oddKTheoryLoopConjugator (B := B)) :=
  (continuous_oddKTheoryReflectionPhaseOperator 0).mul
    (continuous_oddKTheoryReflectionPhaseOperator (-1))

/-- Move just the actual zero coefficient coordinate from -1 to +1. -/
def oddKTheoryCrossingOperator (t : ℝ) : OddKTheoryStandardOperator B :=
  oddKTheorySignOperator + (2 * (t : ℂ)) • oddKTheoryZeroProjection

theorem oddKTheoryCrossingOperator_star (t : ℝ) :
    star (oddKTheoryCrossingOperator (B := B) t) = oddKTheoryCrossingOperator t := by
  simp only [oddKTheoryCrossingOperator, star_add, star_smul,
    oddKTheorySignOperator_star, oddKTheoryZeroProjection_star,
    star_mul, star_ofNat, Complex.star_def, Complex.conj_ofReal]
  rw [mul_comm (t : ℂ) (2 : ℂ)]

theorem oddKTheoryCrossingOperator_square (t : ℝ) :
    oddKTheoryCrossingOperator (B := B) t * oddKTheoryCrossingOperator t =
      1 + (-4 * (t : ℂ) * (1 - (t : ℂ))) • oddKTheoryZeroProjection := by
  simp only [oddKTheoryCrossingOperator, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, oddKTheorySignOperator_square,
    oddKTheorySign_mul_zeroProjection, oddKTheoryZeroProjection_mul_sign,
    oddKTheoryZeroProjection_square]
  module

/-- An actual norm-continuous selfadjoint infinite-module loop. -/
def oddKTheoryUniversalFredholmLoop (t : ℝ) : OddKTheoryStandardOperator B :=
  star (oddKTheoryLoopConjugator (B := B) t : OddKTheoryStandardOperator B) *
    oddKTheoryCrossingOperator (B := B) t *
      (oddKTheoryLoopConjugator (B := B) t : OddKTheoryStandardOperator B)

theorem continuous_oddKTheoryUniversalFredholmLoop :
    Continuous (oddKTheoryUniversalFredholmLoop (B := B)) := by
  unfold oddKTheoryUniversalFredholmLoop oddKTheoryCrossingOperator
  have hV : Continuous (fun t =>
      (oddKTheoryLoopConjugator (B := B) t : OddKTheoryStandardOperator B)) :=
    continuous_subtype_val.comp continuous_oddKTheoryLoopConjugator
  exact (hV.star.mul (by fun_prop)).mul hV

theorem oddKTheoryUniversalFredholmLoop_isSelfAdjoint (t : ℝ) :
    IsSelfAdjoint (oddKTheoryUniversalFredholmLoop (B := B) t) := by
  change star (oddKTheoryUniversalFredholmLoop (B := B) t) = _
  simp only [oddKTheoryUniversalFredholmLoop, star_mul, star_star,
    oddKTheoryCrossingOperator_star, mul_assoc]

@[simp] theorem oddKTheoryUniversalFredholmLoop_zero :
    oddKTheoryUniversalFredholmLoop (B := B) 0 = oddKTheorySignOperator := by
  simp [oddKTheoryUniversalFredholmLoop, oddKTheoryLoopConjugator, oddKTheoryCrossingOperator]

/-- The two actual integer reflections make the upper endpoint the same sign
operator. This is an operator identity on the genuine completed module. -/
@[simp] theorem oddKTheoryUniversalFredholmLoop_one :
    oddKTheoryUniversalFredholmLoop (B := B) 1 = oddKTheorySignOperator := by
  simp only [oddKTheoryUniversalFredholmLoop, oddKTheoryLoopConjugator, Submonoid.coe_mul,
    oddKTheoryReflectionPhaseOperator_one_coe, star_mul, oddKTheoryReflectionOperator_star,
    oddKTheoryCrossingOperator, Complex.ofReal_one, mul_one]
  have hzero : oddKTheoryReflectionOperator (B := B) 0 *
      (oddKTheorySignOperator + (2 : ℂ) • oddKTheoryZeroProjection) *
      oddKTheoryReflectionOperator 0 = -oddKTheorySignOperator := by
    rw [mul_add, add_mul, oddKTheoryReflection_zero_sign_conjugate,
      mul_smul_comm, oddKTheoryReflection_zero_mul_zeroProjection, smul_mul_assoc,
      oddKTheoryZeroProjection_mul_reflection_zero]
    module
  calc
    _ = oddKTheoryReflectionOperator (-1) *
        (oddKTheoryReflectionOperator 0 *
          (oddKTheorySignOperator + (2 : ℂ) • oddKTheoryZeroProjection) *
          oddKTheoryReflectionOperator 0) * oddKTheoryReflectionOperator (-1) := by
      simp only [mul_assoc]
    _ = oddKTheorySignOperator := by
      rw [hzero, mul_neg, neg_mul, oddKTheoryReflection_neg_one_sign_conjugate, neg_neg]

/-- The exact square defect of the actual loop. No compactness of the zero
coordinate projection is asserted by this identity. -/
theorem oddKTheoryUniversalFredholmLoop_square_defect (t : ℝ) :
    oddKTheoryUniversalFredholmLoop (B := B) t * oddKTheoryUniversalFredholmLoop t - 1 =
      (-4 * (t : ℂ) * (1 - (t : ℂ))) •
        (star (oddKTheoryLoopConjugator (B := B) t : OddKTheoryStandardOperator B) *
          oddKTheoryZeroProjection *
            (oddKTheoryLoopConjugator (B := B) t : OddKTheoryStandardOperator B)) := by
  let V := oddKTheoryLoopConjugator (B := B) t
  let T := oddKTheoryCrossingOperator (B := B) t
  have hVV : (V : OddKTheoryStandardOperator B) * star (V : OddKTheoryStandardOperator B) = 1 :=
    Unitary.coe_mul_star_self V
  have hVV' : star (V : OddKTheoryStandardOperator B) * (V : OddKTheoryStandardOperator B) = 1 :=
    Unitary.coe_star_mul_self V
  change (star (V : OddKTheoryStandardOperator B) * T * (V : OddKTheoryStandardOperator B)) *
    (star (V : OddKTheoryStandardOperator B) * T * (V : OddKTheoryStandardOperator B)) - 1 = _
  calc
    _ = star (V : OddKTheoryStandardOperator B) * T *
        ((V : OddKTheoryStandardOperator B) * star (V : OddKTheoryStandardOperator B)) * T *
          (V : OddKTheoryStandardOperator B) - 1 := by
      simp only [mul_assoc]
    _ = star (V : OddKTheoryStandardOperator B) * (T * T - 1) *
        (V : OddKTheoryStandardOperator B) := by
      rw [hVV, mul_one, mul_sub, sub_mul, mul_one, hVV']
      simp only [mul_assoc]
    _ = (-4 * (t : ℂ) * (1 - (t : ℂ))) •
        (star (V : OddKTheoryStandardOperator B) * oddKTheoryZeroProjection *
          (V : OddKTheoryStandardOperator B)) := by
      rw [oddKTheoryCrossingOperator_square, add_sub_cancel_left,
        mul_smul_comm, smul_mul_assoc]

end BC4lean.KKTheory
