import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Positive semidefinite coefficient-valued module forms

The algebraic inner-product laws and positivity alone give the C⋆-valued
Cauchy–Schwarz inequality. No norm or nondegeneracy on the vector space is
assumed. The proof regularizes the squared length by a positive real epsilon
and then passes to zero using the closed coefficient order.

The null vectors form a complex submodule preserved by the right coefficient
action. The square-root diagonal defines a genuine seminorm. These results
provide the prerequisites for quotienting an evaluated module form to obtain
an actual fibre Hilbert module.
-/

noncomputable section

namespace BC4lean.KKTheory

open scoped Topology

/-- A positive semidefinite form for a right module. Its values lie in the
opposite coefficient algebra, consistently with Mathlib's `CStarModule`.
Neither a vector-space norm nor definiteness is required. -/
class PositiveModuleForm (B E : Type*) [NonUnitalCStarAlgebra B] [PartialOrder B]
    [AddCommGroup E] [Module ℂ E] [SMul Bᵐᵒᵖ E] extends Inner Bᵐᵒᵖ E where
  inner_add_right {x y z} : inner x (y + z) = inner x y + inner x z
  inner_self_nonneg {x} : 0 ≤ inner x x
  inner_op_smul_right {a : Bᵐᵒᵖ} {x y} : inner x (a • y) = a * inner x y
  inner_smul_right_complex {c : ℂ} {x y} : inner x (c • y) = c • inner x y
  star_inner x y : star (inner x y) = inner y x

attribute [simp] PositiveModuleForm.inner_add_right PositiveModuleForm.inner_op_smul_right
  PositiveModuleForm.inner_smul_right_complex PositiveModuleForm.star_inner

namespace PositiveModuleForm

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [AddCommGroup E] [Module ℂ E] [SMul Bᵐᵒᵖ E] [PositiveModuleForm B E]

local notation "⟪" x ", " y "⟫" => inner Bᵐᵒᵖ x y

@[simp] theorem inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ := by
  rw [← star_star (r := ⟪x + y, z⟫)]
  simp only [inner_add_right, star_add, star_inner]

@[simp] theorem inner_op_smul_left (a : Bᵐᵒᵖ) (x y : E) :
    ⟪a • x, y⟫ = ⟪x, y⟫ * star a := by
  rw [← star_inner]
  simp

@[simp] theorem inner_smul_left_complex (c : ℂ) (x y : E) :
    ⟪c • x, y⟫ = star c • ⟪x, y⟫ := by
  rw [← star_inner]
  simp

@[simp] theorem inner_smul_left_real (c : ℝ) (x y : E) :
    ⟪c • x, y⟫ = c • ⟪x, y⟫ := by
  have h : c • x = (c : ℂ) • x := by simp
  rw [h, inner_smul_left_complex]
  simp

@[simp] theorem inner_smul_right_real (c : ℝ) (x y : E) :
    ⟪x, c • y⟫ = c • ⟪x, y⟫ := by
  have h : c • y = (c : ℂ) • y := by simp
  rw [h, inner_smul_right_complex]
  simp

/-- The form as an actual sesquilinear map. -/
def innerSesquilinear : E →ₗ⋆[ℂ] E →ₗ[ℂ] Bᵐᵒᵖ where
  toFun x :=
    { toFun := fun y => ⟪x, y⟫
      map_add' := fun _ _ => by simp
      map_smul' := fun _ _ => by simp }
  map_add' := fun _ _ => by ext; simp
  map_smul' := fun _ _ => by ext; simp

@[simp] theorem innerSesquilinear_apply (x y : E) :
    innerSesquilinear (B := B) x y = ⟪x, y⟫ := rfl

@[simp] theorem inner_zero_right (x : E) : ⟪x, 0⟫ = 0 := by
  simp [← innerSesquilinear_apply]

@[simp] theorem inner_zero_left (x : E) : ⟪0, x⟫ = 0 := by
  simp [← innerSesquilinear_apply]

@[simp] theorem inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫ := by
  simp [← innerSesquilinear_apply]

@[simp] theorem inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫ := by
  simp [← innerSesquilinear_apply]

@[simp] theorem inner_sub_right (x y z : E) :
    ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp [← innerSesquilinear_apply]

@[simp] theorem inner_sub_left (x y z : E) :
    ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp [← innerSesquilinear_apply]

@[simp] theorem isSelfAdjoint_inner_self (x : E) : IsSelfAdjoint ⟪x, x⟫ :=
  star_inner x x

variable [StarOrderedRing B]

/-- Regularized C⋆-Cauchy–Schwarz. The only scalar division implicit in
cancelling scalar multiplication uses the strictly positive regularization. -/
theorem inner_mul_inner_swap_le_add (x y : E) (ε : ℝ) (hε : 0 < ε) :
    ⟪x, y⟫ * ⟪y, x⟫ ≤ (‖⟪x, x⟫‖ + ε) • ⟪y, y⟫ := by
  let μ : ℝ := ‖⟪x, x⟫‖ + ε
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hbound (a : Bᵐᵒᵖ) : a * ⟪x, x⟫ * star a ≤ μ • (a * star a) := by
    calc
      a * ⟪x, x⟫ * star a ≤ ‖⟪x, x⟫‖ • (a * star a) :=
        CStarAlgebra.star_right_conjugate_le_norm_smul (isSelfAdjoint_inner_self x)
      _ ≤ μ • (a * star a) :=
        smul_le_smul_of_nonneg_right (by dsimp [μ]; linarith)
          (mul_star_self_nonneg a)
  have hquad (a : Bᵐᵒᵖ) : (0 : Bᵐᵒᵖ) ≤
      μ • (a * star a) - μ • (a * ⟪y, x⟫) - μ • (⟪x, y⟫ * star a) +
        μ • (μ • ⟪y, y⟫) := by
    calc
      (0 : Bᵐᵒᵖ) ≤ ⟪a • x - μ • y, a • x - μ • y⟫ := inner_self_nonneg
      _ = a * ⟪x, x⟫ * star a - μ • (a * ⟪y, x⟫) -
          μ • (⟪x, y⟫ * star a) + μ • (μ • ⟪y, y⟫) := by
        simp only [inner_sub_right, inner_op_smul_right, inner_sub_left,
          inner_op_smul_left, inner_smul_left_real, mul_sub, mul_smul_comm,
          inner_smul_right_real, smul_sub, mul_assoc]
        abel
      _ ≤ μ • (a * star a) - μ • (a * ⟪y, x⟫) -
          μ • (⟪x, y⟫ * star a) + μ • (μ • ⟪y, y⟫) := by
        gcongr
        exact hbound a
  have h := hquad ⟪x, y⟫
  simp only [star_inner, sub_self, zero_sub, le_neg_add_iff_add_le, add_zero] at h
  rwa [smul_le_smul_iff_of_pos_left hμ] at h

/-- The genuine C⋆-algebra-valued Cauchy–Schwarz inequality for a semidefinite
form. Passing epsilon to zero uses the actual closed coefficient order. -/
theorem inner_mul_inner_swap_le (x y : E) :
    ⟪x, y⟫ * ⟪y, x⟫ ≤ ‖⟪x, x⟫‖ • ⟪y, y⟫ := by
  have hc : Filter.Tendsto (fun _ : ℕ => ‖⟪x, x⟫‖)
      Filter.atTop (𝓝 ‖⟪x, x⟫‖) := tendsto_const_nhds
  have hy : Filter.Tendsto (fun _ : ℕ => ⟪y, y⟫)
      Filter.atTop (𝓝 ⟪y, y⟫) := tendsto_const_nhds
  have hlim : Filter.Tendsto
      (fun n : ℕ => (‖⟪x, x⟫‖ + 1 / ((n : ℝ) + 1)) • ⟪y, y⟫)
      Filter.atTop (𝓝 (‖⟪x, x⟫‖ • ⟪y, y⟫)) := by
    simpa only [add_zero] using
      (hc.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).smul hy
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun n =>
    inner_mul_inner_swap_le_add x y (1 / ((n : ℝ) + 1)) (by positivity))

/-- The length defined by the diagonal of the form. -/
def formNorm (x : E) : ℝ := Real.sqrt ‖⟪x, x⟫‖

omit [StarOrderedRing B] in
theorem formNorm_nonneg (x : E) : 0 ≤ formNorm (B := B) x := Real.sqrt_nonneg _

omit [StarOrderedRing B] in
@[simp] theorem formNorm_sq (x : E) : (formNorm (B := B) x) ^ 2 = ‖⟪x, x⟫‖ :=
  Real.sq_sqrt (norm_nonneg _)

omit [StarOrderedRing B] in
@[simp] theorem formNorm_zero : formNorm (B := B) (0 : E) = 0 := by simp [formNorm]

/-- Norm Cauchy–Schwarz, with the lengths actually defined by the form. -/
theorem norm_inner_le (x y : E) :
    ‖⟪x, y⟫‖ ≤ formNorm (B := B) x * formNorm (B := B) y := by
  have h : ‖⟪x, y⟫‖ ^ 2 ≤ (formNorm (B := B) x * formNorm (B := B) y) ^ 2 := by
    calc
      ‖⟪x, y⟫‖ ^ 2 = ‖⟪x, y⟫ * ⟪y, x⟫‖ := by
        rw [← star_inner x, CStarRing.norm_self_mul_star, pow_two]
      _ ≤ ‖‖⟪x, x⟫‖ • ⟪y, y⟫‖ := by
        apply CStarAlgebra.norm_le_norm_of_nonneg_of_le _ (inner_mul_inner_swap_le x y)
        rw [← star_inner x]
        exact mul_star_self_nonneg (⟪x, y⟫)
      _ = ‖⟪x, x⟫‖ * ‖⟪y, y⟫‖ := by simp [norm_smul]
      _ = (formNorm (B := B) x) ^ 2 * (formNorm (B := B) y) ^ 2 := by
        rw [formNorm_sq, formNorm_sq]
      _ = (formNorm (B := B) x * formNorm (B := B) y) ^ 2 := by rw [mul_pow]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (formNorm_nonneg x) (formNorm_nonneg y)) (by norm_num)).mp h

/-- A null diagonal is equivalent to vanishing against every vector. -/
theorem inner_self_eq_zero_iff (x : E) :
    ⟪x, x⟫ = 0 ↔ ∀ y, ⟪x, y⟫ = 0 := by
  refine ⟨fun hx y => ?_, fun hx => hx x⟩
  have h := norm_inner_le (B := B) x y
  have hzero : formNorm (B := B) x = 0 := by simp [formNorm, hx]
  rw [hzero, zero_mul] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

/-- The actual radical, expressed as the vectors annihilating the entire form. -/
def nullRadical : Submodule ℂ E where
  carrier := {x | ∀ y, ⟪x, y⟫ = 0}
  zero_mem' := fun y => inner_zero_left y
  add_mem' := fun hx hy y => by simp [hx y, hy y]
  smul_mem' := fun c x hx y => by simp [hx y]

@[simp] theorem mem_nullRadical (x : E) :
    x ∈ nullRadical (B := B) (E := E) ↔ ⟪x, x⟫ = 0 :=
  (inner_self_eq_zero_iff x).symm

omit [StarOrderedRing B] in
/-- The right coefficient action preserves the null radical. -/
theorem op_smul_mem_nullRadical (a : Bᵐᵒᵖ) (x : E)
    (hx : x ∈ nullRadical (B := B) (E := E)) :
    a • x ∈ nullRadical (B := B) (E := E) := by
  change ∀ y, ⟪a • x, y⟫ = 0
  intro y
  rw [inner_op_smul_left, hx y, zero_mul]

omit [StarOrderedRing B] in
/-- Coefficient multiplication respects radical cosets without assuming that
the unquotiented coefficient action is distributive. -/
theorem op_smul_sub_mem_nullRadical (a : Bᵐᵒᵖ) {x x' : E}
    (hx : x - x' ∈ nullRadical (B := B) (E := E)) :
    a • x - a • x' ∈ nullRadical (B := B) (E := E) := by
  change ∀ y, ⟪a • x - a • x', y⟫ = 0
  intro y
  rw [inner_sub_left, inner_op_smul_left, inner_op_smul_left,
    ← sub_mul, ← inner_sub_left, hx y, zero_mul]

omit [StarOrderedRing B] in
/-- Changing the first input by a radical vector preserves the form. -/
theorem inner_eq_of_sub_mem_left {x x' y : E}
    (hx : x - x' ∈ nullRadical (B := B) (E := E)) : ⟪x, y⟫ = ⟪x', y⟫ := by
  apply sub_eq_zero.mp
  rw [← inner_sub_left]
  exact hx y

omit [StarOrderedRing B] in
/-- Changing the second input by a radical vector preserves the form. -/
theorem inner_eq_of_sub_mem_right {x y y' : E}
    (hy : y - y' ∈ nullRadical (B := B) (E := E)) : ⟪x, y⟫ = ⟪x, y'⟫ := by
  apply sub_eq_zero.mp
  rw [← inner_sub_right, ← star_inner (y - y') x, hy x, star_zero]

omit [StarOrderedRing B] in
/-- The diagonal length is constant on the actual radical cosets. -/
theorem formNorm_eq_of_sub_mem {x x' : E}
    (hx : x - x' ∈ nullRadical (B := B) (E := E)) :
    formNorm (B := B) x = formNorm (B := B) x' := by
  have hinner : ⟪x, x⟫ = ⟪x', x'⟫ :=
    (inner_eq_of_sub_mem_left hx).trans (inner_eq_of_sub_mem_right hx)
  simp only [formNorm, hinner]

/-- The diagonal length satisfies the triangle inequality even before quotient. -/
theorem formNorm_triangle (x y : E) :
    formNorm (B := B) (x + y) ≤ formNorm (B := B) x + formNorm (B := B) y := by
  have h : (formNorm (B := B) (x + y)) ^ 2 ≤
      (formNorm (B := B) x + formNorm (B := B) y) ^ 2 := by
    calc
      (formNorm (B := B) (x + y)) ^ 2 ≤
          ‖⟪x, x⟫ + ⟪y, x⟫‖ + ‖⟪x, y⟫‖ + ‖⟪y, y⟫‖ := by
        rw [formNorm_sq, inner_add_right, inner_add_left, inner_add_left, ← add_assoc]
        exact norm_add₃_le
      _ ≤ ‖⟪x, x⟫‖ + ‖⟪y, x⟫‖ + ‖⟪x, y⟫‖ + ‖⟪y, y⟫‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ‖⟪x, x⟫‖ + formNorm (B := B) y * formNorm (B := B) x +
          formNorm (B := B) x * formNorm (B := B) y + ‖⟪y, y⟫‖ := by
        gcongr <;> exact norm_inner_le _ _
      _ = (formNorm (B := B) x) ^ 2 + formNorm (B := B) y * formNorm (B := B) x +
          formNorm (B := B) x * formNorm (B := B) y + (formNorm (B := B) y) ^ 2 := by
        rw [formNorm_sq, formNorm_sq]
      _ = (formNorm (B := B) x + formNorm (B := B) y) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (formNorm_nonneg _)
    (add_nonneg (formNorm_nonneg _) (formNorm_nonneg _)) (by norm_num)).mp h

omit [StarOrderedRing B] in
@[simp] theorem formNorm_smul (c : ℂ) (x : E) :
    formNorm (B := B) (c • x) = ‖c‖ * formNorm (B := B) x := by
  simp [formNorm, norm_smul, ← mul_assoc]

omit [StarOrderedRing B] in
@[simp] theorem formNorm_neg (x : E) : formNorm (B := B) (-x) = formNorm (B := B) x := by
  simp [formNorm]

omit [StarOrderedRing B] in
/-- The right coefficient action is bounded for the proved form length. -/
theorem formNorm_op_smul_le (a : Bᵐᵒᵖ) (x : E) :
    formNorm (B := B) (a • x) ≤ ‖a‖ * formNorm (B := B) x := by
  have h : (formNorm (B := B) (a • x)) ^ 2 ≤
      (‖a‖ * formNorm (B := B) x) ^ 2 := by
    calc
      (formNorm (B := B) (a • x)) ^ 2 = ‖a * ⟪x, x⟫ * star a‖ := by
        rw [formNorm_sq, inner_op_smul_right, inner_op_smul_left, ← mul_assoc]
      _ ≤ ‖a‖ * ‖⟪x, x⟫‖ * ‖star a‖ := norm_mul₃_le
      _ = (‖a‖ * formNorm (B := B) x) ^ 2 := by
        rw [norm_star, ← formNorm_sq]
        ring
  exact (pow_le_pow_iff_left₀ (formNorm_nonneg _)
    (mul_nonneg (norm_nonneg _) (formNorm_nonneg _)) (by norm_num)).mp h

/-- The form determines a genuine bundled complex seminorm. -/
def seminorm : Seminorm ℂ E where
  toFun := formNorm (B := B)
  map_zero' := formNorm_zero
  add_le' := formNorm_triangle
  neg' := formNorm_neg
  smul' := formNorm_smul

@[simp] theorem seminorm_apply (x : E) : seminorm (B := B) x = formNorm (B := B) x := rfl

theorem formNorm_eq_zero_iff (x : E) :
    formNorm (B := B) x = 0 ↔ x ∈ nullRadical (B := B) (E := E) := by
  rw [mem_nullRadical]
  simp [formNorm]

/-- A chosen norm equal to the form length inherits the proved seminorm laws. -/
theorem seminormedSpaceCore [Norm E] (hnorm : ∀ x : E, ‖x‖ = formNorm (B := B) x) :
    SeminormedSpace.Core ℂ E where
  norm_nonneg x := by rw [hnorm]; exact formNorm_nonneg x
  norm_smul c x := by rw [hnorm, hnorm, formNorm_smul]
  norm_triangle x y := by rw [hnorm, hnorm, hnorm]; exact formNorm_triangle x y

/-- Once the radical has been removed and definiteness proved, the same form
gives Mathlib's normed-space core without an additional inequality assumption. -/
theorem normedSpaceCore [Norm E] (hnorm : ∀ x : E, ‖x‖ = formNorm (B := B) x)
    (hdefinite : ∀ x : E, ⟪x, x⟫ = 0 → x = 0) : NormedSpace.Core ℂ E where
  __ := seminormedSpaceCore hnorm
  norm_eq_zero_iff x := by
    rw [hnorm, formNorm_eq_zero_iff, mem_nullRadical]
    exact ⟨hdefinite x, fun hx => by simp [hx]⟩

/-- The proved algebraic and metric laws give a Hilbert-module structure after
an actual quotient has supplied definiteness. No quotient is assumed to exist. -/
@[instance_reducible] def toCStarModule [Norm E] (hnorm : ∀ x : E, ‖x‖ = formNorm (B := B) x)
    (hdefinite : ∀ x : E, ⟪x, x⟫ = 0 → x = 0) : CStarModule Bᵐᵒᵖ E where
  inner := inner Bᵐᵒᵖ
  inner_add_right := inner_add_right
  inner_self_nonneg := inner_self_nonneg
  inner_self := by
    intro x
    exact ⟨hdefinite x, fun hx => by simp [hx]⟩
  inner_op_smul_right := inner_op_smul_right
  inner_smul_right_complex := inner_smul_right_complex
  star_inner := star_inner
  norm_eq_sqrt_norm_inner_self := hnorm

end PositiveModuleForm

end BC4lean.KKTheory
