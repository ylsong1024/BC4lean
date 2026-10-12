import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Topology.Path

/-! # Actual continuous coefficient concatenation

The two half-interval maps and ordinary continuous path concatenation give
joining of matching possibly nonunital coefficient functions. Restriction to
each half recovers the original function, and the uniform norm is their maximum.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B : Type*} [NonUnitalCStarAlgebra B]

/-- The first half of the interval, parametrized by the entire unit interval. -/
def intervalLeftHalf : C(unitInterval, unitInterval) where
  toFun t := ⟨(t : ℝ) / 2, by
    constructor <;> linarith [t.property.1, t.property.2]⟩
  continuous_toFun := by fun_prop

/-- The second half of the interval, parametrized by the entire unit interval. -/
def intervalRightHalf : C(unitInterval, unitInterval) where
  toFun t := ⟨((t : ℝ) + 1) / 2, by
    constructor <;> linarith [t.property.1, t.property.2]⟩
  continuous_toFun := by fun_prop

@[simp] theorem intervalLeftHalf_coe (t : unitInterval) :
    (intervalLeftHalf t : ℝ) = (t : ℝ) / 2 := rfl

@[simp] theorem intervalRightHalf_coe (t : unitInterval) :
    (intervalRightHalf t : ℝ) = ((t : ℝ) + 1) / 2 := rfl

@[simp] theorem intervalLeftHalf_zero : intervalLeftHalf 0 = 0 := by
  apply Subtype.ext
  norm_num [intervalLeftHalf]

@[simp] theorem intervalRightHalf_one : intervalRightHalf 1 = 1 := by
  apply Subtype.ext
  norm_num [intervalRightHalf]

/-- Join two actual continuous coefficient functions agreeing at their common
endpoint, by the usual continuous path concatenation. -/
def intervalCoefficientJoin (f g : C(unitInterval, B)) (h : f 1 = g 0) :
    C(unitInterval, B) :=
  ((Path.mk f rfl rfl : Path (f 0) (f 1)).trans
    (Path.mk g h.symm rfl : Path (f 1) (g 1))).toContinuousMap

theorem intervalCoefficientJoin_apply (f g : C(unitInterval, B)) (h : f 1 = g 0)
    (t : unitInterval) :
    intervalCoefficientJoin f g h t =
      if ht : (t : ℝ) ≤ 1 / 2 then
        f ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.property.1, ht⟩⟩
      else
        g ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
          ⟨(not_le.1 ht).le, t.property.2⟩⟩ := by
  exact Path.trans_apply _ _ t

@[simp] theorem intervalCoefficientJoin_zero (f g : C(unitInterval, B)) (h : f 1 = g 0) :
    intervalCoefficientJoin f g h 0 = f 0 :=
  Path.source _

@[simp] theorem intervalCoefficientJoin_one (f g : C(unitInterval, B)) (h : f 1 = g 0) :
    intervalCoefficientJoin f g h 1 = g 1 :=
  Path.target _

/-- Restricting the joined function to its first half recovers the first
continuous function at every parameter, including the common endpoint. -/
@[simp] theorem intervalCoefficientJoin_leftHalf (f g : C(unitInterval, B))
    (h : f 1 = g 0) (t : unitInterval) :
    intervalCoefficientJoin f g h (intervalLeftHalf t) = f t := by
  rw [intervalCoefficientJoin_apply]
  have ht : (intervalLeftHalf t : ℝ) ≤ 1 / 2 := by
    change (t : ℝ) / 2 ≤ 1 / 2
    linarith [t.property.2]
  rw [dif_pos ht]
  congr 1
  apply Subtype.ext
  change 2 * ((t : ℝ) / 2) = (t : ℝ)
  ring

/-- Restricting the joined function to its second half recovers the second
continuous function; agreement at the seam handles the zero parameter. -/
@[simp] theorem intervalCoefficientJoin_rightHalf (f g : C(unitInterval, B))
    (h : f 1 = g 0) (t : unitInterval) :
    intervalCoefficientJoin f g h (intervalRightHalf t) = g t := by
  rw [intervalCoefficientJoin_apply]
  by_cases ht : (intervalRightHalf t : ℝ) ≤ 1 / 2
  · rw [dif_pos ht]
    have hzero : (t : ℝ) = 0 := by
      change ((t : ℝ) + 1) / 2 ≤ 1 / 2 at ht
      linarith [t.property.1]
    have htzero : t = 0 := Subtype.ext hzero
    subst t
    calc
      _ = f 1 := by
        congr 1
        apply Subtype.ext
        norm_num [intervalRightHalf]
      _ = g 0 := h
  · rw [dif_neg ht]
    congr 1
    apply Subtype.ext
    change 2 * (((t : ℝ) + 1) / 2) - 1 = (t : ℝ)
    ring

/-- The norm of a continuous function joined at the seam is exactly the
maximum of the two original uniform norms. -/
theorem intervalCoefficientJoin_norm (f g : C(unitInterval, B)) (h : f 1 = g 0) :
    ‖intervalCoefficientJoin f g h‖ = max ‖f‖ ‖g‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (le_trans (norm_nonneg f) (le_max_left _ _))).mpr
    intro t
    rw [intervalCoefficientJoin_apply]
    split_ifs
    · exact (f.norm_coe_le_norm _).trans (le_max_left _ _)
    · exact (g.norm_coe_le_norm _).trans (le_max_right _ _)
  · apply max_le
    · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
      intro t
      rw [← intervalCoefficientJoin_leftHalf f g h t]
      exact (intervalCoefficientJoin f g h).norm_coe_le_norm _
    · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
      intro t
      rw [← intervalCoefficientJoin_rightHalf f g h t]
      exact (intervalCoefficientJoin f g h).norm_coe_le_norm _

/-- A continuous function is determined by its two half-interval restrictions. -/
theorem continuousIntervalHalves_ext {f g : C(unitInterval, B)}
    (hl : ∀ t, f (intervalLeftHalf t) = g (intervalLeftHalf t))
    (hr : ∀ t, f (intervalRightHalf t) = g (intervalRightHalf t)) : f = g := by
  ext t
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · let s : unitInterval :=
      ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.property.1, ht⟩⟩
    have hs : intervalLeftHalf s = t := by
      apply Subtype.ext
      change (2 * (t : ℝ)) / 2 = (t : ℝ)
      ring
    simpa only [hs] using hl s
  · let s : unitInterval :=
      ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
        ⟨(not_le.1 ht).le, t.property.2⟩⟩
    have hs : intervalRightHalf s = t := by
      apply Subtype.ext
      change (2 * (t : ℝ) - 1 + 1) / 2 = (t : ℝ)
      ring
    simpa only [hs] using hr s

end BC4lean.KKTheory
