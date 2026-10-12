import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

/-! # The scalar resolution used to turn dense synthesis into a Parseval frame

The functions `eₙ(t) = nt/(1+nt)` increase from zero towards one on the
positive half-line. Their successive differences factor as `t fₙ(t)²`,
where `fₙ(t) = ((1+(n+1)t)(1+nt))⁻¹ᐟ²`. The residual has the quantitative
bound `t(1-eₙ₊₁(t))² ≤ 1/(n+1)`. All functions are extended continuously
to the real line using the positive part; this avoids poles away from the
positive spectrum. No frame or connection existence is assumed here.
-/

noncomputable section
namespace BC4lean.KKTheory

/-- Positive-part extension of the increasing spectral resolution. -/
def standardFrameCutoff (n : ℕ) (t : ℝ) : ℝ :=
  (n : ℝ) * max 0 t / (1 + (n : ℝ) * max 0 t)

/-- Positive-part extension of its residual. -/
def standardFrameResidual (n : ℕ) (t : ℝ) : ℝ :=
  1 / (1 + (n : ℝ) * max 0 t)

/-- The actual scalar square-root band giving the difference of two cutoffs. -/
def standardFrameBand (n : ℕ) (t : ℝ) : ℝ :=
  1 / Real.sqrt ((1 + ((n : ℝ) + 1) * max 0 t) * (1 + (n : ℝ) * max 0 t))

theorem standardFrame_denominator_pos (n : ℕ) (t : ℝ) :
    0 < 1 + (n : ℝ) * max 0 t := by
  positivity

@[fun_prop] theorem continuous_standardFrameCutoff (n : ℕ) :
    Continuous (standardFrameCutoff n) :=
  (continuous_const.mul (continuous_const.max continuous_id)).div
    (continuous_const.add (continuous_const.mul (continuous_const.max continuous_id)))
    (fun t => (standardFrame_denominator_pos n t).ne')

@[fun_prop] theorem continuous_standardFrameResidual (n : ℕ) :
    Continuous (standardFrameResidual n) :=
  continuous_const.div
    (continuous_const.add (continuous_const.mul (continuous_const.max continuous_id)))
    (fun t => (standardFrame_denominator_pos n t).ne')

theorem standardFrame_band_denominator_pos (n : ℕ) (t : ℝ) :
    0 < Real.sqrt ((1 + ((n : ℝ) + 1) * max 0 t) * (1 + (n : ℝ) * max 0 t)) := by
  apply Real.sqrt_pos.mpr
  positivity

@[fun_prop] theorem continuous_standardFrameBand (n : ℕ) :
    Continuous (standardFrameBand n) :=
  continuous_const.div
    (Real.continuous_sqrt.comp
      ((continuous_const.add (continuous_const.mul (continuous_const.max continuous_id))).mul
        (continuous_const.add (continuous_const.mul (continuous_const.max continuous_id)))))
    (fun t => (standardFrame_band_denominator_pos n t).ne')

@[simp] theorem standardFrameCutoff_zero (t : ℝ) : standardFrameCutoff 0 t = 0 := by
  simp [standardFrameCutoff]

@[simp] theorem standardFrameCutoff_at_zero (n : ℕ) : standardFrameCutoff n 0 = 0 := by
  simp [standardFrameCutoff]

theorem standardFrameResidual_nonneg (n : ℕ) (t : ℝ) :
    0 ≤ standardFrameResidual n t :=
  div_nonneg zero_le_one (standardFrame_denominator_pos n t).le

theorem standardFrameResidual_le_one (n : ℕ) (t : ℝ) :
    standardFrameResidual n t ≤ 1 := by
  apply (div_le_one (standardFrame_denominator_pos n t)).mpr
  have hp : 0 ≤ (n : ℝ) * max 0 t := by positivity
  linarith

theorem one_sub_standardFrameCutoff (n : ℕ) (t : ℝ) :
    1 - standardFrameCutoff n t = standardFrameResidual n t := by
  dsimp [standardFrameCutoff, standardFrameResidual]
  field_simp [(standardFrame_denominator_pos n t).ne']
  ring

theorem standardFrameCutoff_nonneg (n : ℕ) (t : ℝ) :
    0 ≤ standardFrameCutoff n t := by
  dsimp [standardFrameCutoff]
  positivity

theorem standardFrameCutoff_le_one (n : ℕ) (t : ℝ) :
    standardFrameCutoff n t ≤ 1 := by
  have h := standardFrameResidual_nonneg n t
  rw [← one_sub_standardFrameCutoff] at h
  linarith

theorem standardFrameBand_nonneg (n : ℕ) (t : ℝ) :
    0 ≤ standardFrameBand n t :=
  div_nonneg zero_le_one (standardFrame_band_denominator_pos n t).le

/-- Exact scalar telescoping identity, valid even at the zero spectral value. -/
theorem standardFrameBand_square (n : ℕ) (t : ℝ) :
    max 0 t * standardFrameBand n t ^ 2 =
      standardFrameCutoff (n + 1) t - standardFrameCutoff n t := by
  have hs : Real.sqrt ((1 + ((n : ℝ) + 1) * max 0 t) *
      (1 + (n : ℝ) * max 0 t)) ^ 2 =
      (1 + ((n : ℝ) + 1) * max 0 t) * (1 + (n : ℝ) * max 0 t) :=
    Real.sq_sqrt (by positivity)
  simp only [standardFrameBand, standardFrameCutoff, Nat.cast_add, Nat.cast_one, div_pow, one_pow]
  rw [hs]
  field_simp [(standardFrame_denominator_pos n t).ne',
    (standardFrame_denominator_pos (n + 1) t).ne']
  ring

/-- Positivity of the square-root bands proves monotonicity of the resolution. -/
theorem standardFrameCutoff_mono (t : ℝ) : Monotone (fun n => standardFrameCutoff n t) := by
  apply monotone_nat_of_le_succ
  intro n
  apply sub_nonneg.mp
  rw [← standardFrameBand_square]
  positivity

/-- The residual applied to a square-root spectral vector has a uniform rate. -/
theorem standardFrameResidual_square_error_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t * standardFrameResidual (n + 1) t ^ 2 ≤ 1 / ((n : ℝ) + 1) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hd : 0 < 1 + ((n : ℝ) + 1) * t := by positivity
  simp only [standardFrameResidual, max_eq_right ht, Nat.cast_add, Nat.cast_one, div_pow, one_pow]
  rw [mul_one_div]
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) hn).mpr
  nlinarith [sq_nonneg (((n : ℝ) + 1) * t), mul_nonneg hn.le ht]

end BC4lean.KKTheory
