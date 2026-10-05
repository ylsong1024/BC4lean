import Mathlib.Analysis.CStarAlgebra.Module.Constructions

/-! # Right Hilbert C⋆-module foundations

We use `CStarModule Bᵐᵒᵖ E`: the right action `x b` is `MulOpposite.op b • x`,
and the usual B-valued inner product is `MulOpposite.unop (inner Bᵐᵒᵖ x y)`.
This explicit opposite is necessary because the pinned Mathlib convention has
`inner x (a • y) = a * inner x y`. Completeness is an additional
`CompleteSpace E` assumption when a Hilbert (rather than pre-Hilbert) module
is required. The results below also hold before completion and for nonunital B.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace
open CStarModule

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

/-- Nondegeneracy in the first variable. -/
theorem module_inner_ext_left {x y : E}
    (h : ∀ z, ⟪x, z⟫_(Bᵐᵒᵖ) = ⟪y, z⟫_(Bᵐᵒᵖ)) : x = y := by
  apply sub_eq_zero.mp
  apply (CStarModule.inner_self (A := Bᵐᵒᵖ)).mp
  rw [CStarModule.inner_sub_left, h, sub_self]

/-- Nondegeneracy in the second variable. -/
theorem module_inner_ext_right {x y : E}
    (h : ∀ z, ⟪z, x⟫_(Bᵐᵒᵖ) = ⟪z, y⟫_(Bᵐᵒᵖ)) : x = y := by
  apply module_inner_ext_left (B := B)
  intro z
  simpa only [CStarModule.star_inner] using congrArg star (h z)

/-- The scalar action distributes over addition in the coefficient algebra. -/
theorem module_add_smul (a b : Bᵐᵒᵖ) (x : E) : (a + b) • x = a • x + b • x := by
  apply module_inner_ext_right (B := B)
  intro z
  simp only [inner_op_smul_right, CStarModule.inner_add_right, add_mul]

/-- The scalar action distributes over addition in the module. -/
theorem module_smul_add (a : Bᵐᵒᵖ) (x y : E) : a • (x + y) = a • x + a • y := by
  apply module_inner_ext_right (B := B)
  intro z
  simp only [inner_op_smul_right, CStarModule.inner_add_right, mul_add]

/-- Associativity of the right action, expressed with opposite coefficients. -/
theorem module_mul_smul (a b : Bᵐᵒᵖ) (x : E) : (a * b) • x = a • (b • x) := by
  apply module_inner_ext_right (B := B)
  intro z
  simp only [inner_op_smul_right, mul_assoc]

/-- Compatibility of complex multiplication with the coefficient action. -/
theorem module_complex_smul (c : ℂ) (a : Bᵐᵒᵖ) (x : E) :
    (c • a) • x = c • (a • x) := by
  apply module_inner_ext_right (B := B)
  intro z
  simp only [inner_op_smul_right, inner_smul_right_complex, smul_mul_assoc]

/-- The module action is contractive; no bound on it is assumed. -/
theorem module_norm_smul_le (a : Bᵐᵒᵖ) (x : E) : ‖a • x‖ ≤ ‖a‖ * ‖x‖ := by
  have h : ‖a • x‖ ^ 2 ≤ (‖a‖ * ‖x‖) ^ 2 := by
    calc
      ‖a • x‖ ^ 2 = ‖a * ⟪x, x⟫_(Bᵐᵒᵖ) * star a‖ := by
        rw [CStarModule.norm_sq_eq (Bᵐᵒᵖ), inner_op_smul_right, inner_op_smul_left, ← mul_assoc]
      _ ≤ ‖a‖ * ‖⟪x, x⟫_(Bᵐᵒᵖ)‖ * ‖star a‖ := norm_mul₃_le
      _ = (‖a‖ * ‖x‖) ^ 2 := by
        rw [norm_star, ← CStarModule.norm_sq_eq (Bᵐᵒᵖ)]
        ring
  exact (pow_le_pow_iff_left₀ (_root_.norm_nonneg _) (by positivity) (by decide : 2 ≠ 0)).mp h

variable [StarOrderedRing B]

/-- The standard right module over B has the usual B-valued inner product. -/
theorem standard_module_inner (x y : B) :
    MulOpposite.unop ⟪MulOpposite.op x, MulOpposite.op y⟫_(Bᵐᵒᵖ) = star x * y := rfl

omit [PartialOrder B] [StarOrderedRing B] in
/-- The standard right module is complete. -/
theorem standard_module_complete : CompleteSpace Bᵐᵒᵖ := inferInstance

end BC4lean.KKTheory
