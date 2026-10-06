import Mathlib.Analysis.Real.Sqrt

/-! # The scalar cutoff for lifting through C⋆-homomorphisms

For a positive radius `r`, the cutoff is zero below `r²` and removes only a
norm-small part of a positive spectral value: `t * (1 - h(t))² ≤ r²` for
`t ≥ 0`. Its denominator is uniformly positive, so the cutoff is continuous
on the entire real line and vanishes at zero, as needed for nonunital CFC.
-/

noncomputable section
namespace BC4lean.KKTheory

/-- The scalar cutoff at a positive radius. For `r > 0` the displayed value
is nonnegative, so an additional outer `max 0` would give the same function. -/
def cstarHomCutoff (r t : ℝ) : ℝ :=
  1 - r / Real.sqrt (max (r ^ 2) t)

theorem cstarHomCutoff_denominator_pos {r t : ℝ} (hr : 0 < r) :
    0 < Real.sqrt (max (r ^ 2) t) :=
  Real.sqrt_pos.mpr ((pow_pos hr 2).trans_le (le_max_left _ _))

theorem cstarHomCutoff_le_denominator {r t : ℝ} (hr : 0 < r) :
    r ≤ Real.sqrt (max (r ^ 2) t) := by
  calc
    r = Real.sqrt (r ^ 2) := (Real.sqrt_sq hr.le).symm
    _ ≤ Real.sqrt (max (r ^ 2) t) := Real.sqrt_le_sqrt (le_max_left _ _)

@[fun_prop] theorem continuous_cstarHomCutoff {r : ℝ} (hr : 0 < r) :
    Continuous (cstarHomCutoff r) :=
  continuous_const.sub (continuous_const.div
    (Real.continuous_sqrt.comp (continuous_const.max continuous_id))
    (fun _ => (cstarHomCutoff_denominator_pos hr).ne'))

/-- The cutoff vanishes on the entire half-line below the squared radius. -/
theorem cstarHomCutoff_eq_zero_of_le {r t : ℝ} (hr : 0 < r) (ht : t ≤ r ^ 2) :
    cstarHomCutoff r t = 0 := by
  rw [cstarHomCutoff, max_eq_left ht, Real.sqrt_sq hr.le, div_self hr.ne', sub_self]

@[simp] theorem cstarHomCutoff_zero {r : ℝ} (hr : 0 < r) : cstarHomCutoff r 0 = 0 :=
  cstarHomCutoff_eq_zero_of_le hr (sq_nonneg r)

/-- Every cutoff value lies in the real unit interval. -/
theorem cstarHomCutoff_mem_Icc {r t : ℝ} (hr : 0 < r) :
    cstarHomCutoff r t ∈ Set.Icc 0 1 := by
  have hd := cstarHomCutoff_denominator_pos (t := t) hr
  constructor
  · exact sub_nonneg.mpr ((div_le_one hd).mpr (cstarHomCutoff_le_denominator hr))
  · exact sub_le_self 1 (div_nonneg hr.le hd.le)

theorem cstarHomCutoff_nonneg {r t : ℝ} (hr : 0 < r) : 0 ≤ cstarHomCutoff r t :=
  (cstarHomCutoff_mem_Icc hr).1

theorem cstarHomCutoff_le_one {r t : ℝ} (hr : 0 < r) : cstarHomCutoff r t ≤ 1 :=
  (cstarHomCutoff_mem_Icc hr).2

theorem one_sub_cstarHomCutoff (r t : ℝ) :
    1 - cstarHomCutoff r t = r / Real.sqrt (max (r ^ 2) t) :=
  sub_sub_cancel _ _

/-- The removed spectral part has squared length at most the squared radius. -/
theorem cstarHomCutoff_error_le {r t : ℝ} (hr : 0 < r) :
    t * (1 - cstarHomCutoff r t) ^ 2 ≤ r ^ 2 := by
  let d := Real.sqrt (max (r ^ 2) t)
  have hd : 0 < d := cstarHomCutoff_denominator_pos hr
  have hdsq : d ^ 2 = max (r ^ 2) t :=
    Real.sq_sqrt ((sq_nonneg r).trans (le_max_left _ _))
  have ht : t ≤ d ^ 2 := by rw [hdsq]; exact le_max_right _ _
  rw [one_sub_cstarHomCutoff]
  calc
    t * (r / d) ^ 2 ≤ d ^ 2 * (r / d) ^ 2 :=
      mul_le_mul_of_nonneg_right ht (sq_nonneg _)
    _ = (d * (r / d)) ^ 2 := (mul_pow _ _ _).symm
    _ = r ^ 2 := by rw [mul_comm d, div_mul_cancel₀ _ hd.ne']

/-- Positivity and the upper error bound on nonnegative spectral values. -/
theorem cstarHomCutoff_error_mem_Icc {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    t * (1 - cstarHomCutoff r t) ^ 2 ∈ Set.Icc 0 (r ^ 2) :=
  ⟨mul_nonneg ht (sq_nonneg _), cstarHomCutoff_error_le hr⟩

theorem cstarHomCutoff_clipped_square_nonneg {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    0 ≤ t * (1 - cstarHomCutoff r t) ^ 2 :=
  (cstarHomCutoff_error_mem_Icc hr ht).1

theorem cstarHomCutoff_clipped_square_le {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    t * (1 - cstarHomCutoff r t) ^ 2 ≤ r ^ 2 :=
  (cstarHomCutoff_error_mem_Icc hr ht).2

/-- The explicit formula agrees with the nonnegative-part formula often used
to describe this cutoff. -/
theorem cstarHomCutoff_eq_max {r t : ℝ} (hr : 0 < r) :
    cstarHomCutoff r t = max 0 (1 - r / Real.sqrt (max (r ^ 2) t)) :=
  (max_eq_right (cstarHomCutoff_nonneg hr)).symm

end BC4lean.KKTheory
