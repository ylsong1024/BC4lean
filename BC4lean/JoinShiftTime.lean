import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-! # Continuous coefficients for the descending factor-shift homotopy -/
noncomputable section
namespace BC4lean.ProperActions

/-- Factor n shifts during the interval [1/(n+2),1/(n+1)]. -/
def joinShiftCoefficient (n : ℕ) (t : ℝ) : ℝ :=
  min 1 (max 0 (((n : ℝ) + 1) * ((n : ℝ) + 2) * t - ((n : ℝ) + 1)))

theorem joinShiftCoefficient_nonneg (n : ℕ) (t : ℝ) :
    0 ≤ joinShiftCoefficient n t :=
  le_min zero_le_one (le_max_left _ _)

theorem joinShiftCoefficient_le_one (n : ℕ) (t : ℝ) :
    joinShiftCoefficient n t ≤ 1 := min_le_left _ _

theorem continuous_joinShiftCoefficient (n : ℕ) : Continuous (joinShiftCoefficient n) := by
  unfold joinShiftCoefficient
  fun_prop

@[simp] theorem joinShiftCoefficient_zero (n : ℕ) : joinShiftCoefficient n 0 = 0 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp only [joinShiftCoefficient, mul_zero]
  rw [max_eq_left (by linarith), min_eq_right zero_le_one]

@[simp] theorem joinShiftCoefficient_one (n : ℕ) : joinShiftCoefficient n 1 = 1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold joinShiftCoefficient
  rw [min_eq_left]
  apply le_max_of_le_right
  nlinarith

/-- A lower factor can start moving only after its next higher factor has finished. -/
theorem joinShiftCoefficient_next_eq_one (n : ℕ) (t : ℝ)
    (h : 0 < joinShiftCoefficient n t) : joinShiftCoefficient (n+1) t = 1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp : 0 < (((n : ℝ) + 1) * ((n : ℝ) + 2) * t - ((n : ℝ) + 1)) := by
    have hm := lt_of_lt_of_le h (min_le_right 1 _)
    exact (lt_max_iff.mp hm).resolve_left (lt_irrefl 0)
  have hprod : 0 < ((n : ℝ) + 1) * (((n : ℝ) + 2) * t - 1) := by
    nlinarith [hp]
  have ht : 1 < ((n : ℝ) + 2) * t := by
    have hh := (mul_pos_iff.mp hprod).resolve_right (by intro hbad; linarith [hbad.1])
    linarith [hh.2]
  have hmul := mul_lt_mul_of_pos_left ht (by linarith : 0 < (n : ℝ) + 3)
  unfold joinShiftCoefficient
  rw [Nat.cast_add, Nat.cast_one, min_eq_left]
  apply le_max_of_le_right
  nlinarith

theorem joinShiftCoefficient_eq_zero_of_le (n : ℕ) {t : ℝ}
    (ht : t ≤ 1 / ((n : ℝ) + 2)) : joinShiftCoefficient n t = 0 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hb : t * ((n : ℝ) + 2) ≤ 1 := (le_div_iff₀ (by linarith)).mp ht
  have hmul := mul_le_mul_of_nonneg_left hb (by linarith : 0 ≤ (n : ℝ) + 1)
  unfold joinShiftCoefficient
  rw [max_eq_left (by nlinarith), min_eq_right zero_le_one]

theorem joinShiftCoefficient_eq_one_of_ge (n : ℕ) {t : ℝ}
    (ht : 1 / ((n : ℝ) + 1) ≤ t) : joinShiftCoefficient n t = 1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hb : 1 ≤ t * ((n : ℝ) + 1) := (div_le_iff₀ (by linarith)).mp ht
  have hmul := mul_le_mul_of_nonneg_left hb (by linarith : 0 ≤ (n : ℝ) + 2)
  unfold joinShiftCoefficient
  rw [min_eq_left]
  apply le_max_of_le_right
  nlinarith

/-- The ramp coefficient as a continuous unit-interval-valued function. -/
def joinShiftParameter (n : ℕ) (t : ℝ) : unitInterval :=
  ⟨joinShiftCoefficient n t, joinShiftCoefficient_nonneg n t, joinShiftCoefficient_le_one n t⟩

theorem continuous_joinShiftParameter (n : ℕ) : Continuous (joinShiftParameter n) :=
  (continuous_joinShiftCoefficient n).subtype_mk _

@[simp] theorem joinShiftParameter_zero_of_le (n : ℕ) {t : ℝ}
    (ht : t ≤ 1 / ((n : ℝ) + 2)) : joinShiftParameter n t = 0 :=
  Subtype.ext (joinShiftCoefficient_eq_zero_of_le n ht)

@[simp] theorem joinShiftParameter_one_of_ge (n : ℕ) {t : ℝ}
    (ht : 1 / ((n : ℝ) + 1) ≤ t) : joinShiftParameter n t = 1 :=
  Subtype.ext (joinShiftCoefficient_eq_one_of_ge n ht)

end BC4lean.ProperActions
