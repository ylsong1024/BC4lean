import BC4lean.HilbertCStarModule

/-! # Positive quadratic expressions of Hilbert-module Gram coefficients

Finite Gram coefficients satisfy the coefficient-algebra quadratic positivity
test.  The proof rewrites the expression as the actual inner square of a finite
module sum.  This is an independent step toward general interior-tensor
positivity; no tensor positivity is assumed here.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace
open CStarModule

variable {B E ι : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

/-- A finite Gram quadratic expression equals an actual module inner square. -/
theorem moduleGram_quadratic_eq_inner (s : Finset ι) (x : ι → E) (b : ι → B) :
    (∑ i ∈ s, ∑ j ∈ s,
      star (b i) * MulOpposite.unop ⟪x i, x j⟫_(Bᵐᵒᵖ) * b j) =
      MulOpposite.unop
        ⟪∑ i ∈ s, MulOpposite.op (b i) • x i,
          ∑ j ∈ s, MulOpposite.op (b j) • x j⟫_(Bᵐᵒᵖ) := by
  simp only [CStarModule.inner_sum_left, CStarModule.inner_sum_right,
    CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right,
    Finset.unop_sum, MulOpposite.unop_mul, MulOpposite.unop_star,
    MulOpposite.unop_op, mul_assoc, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Every finite quadratic expression in Hilbert-module Gram coefficients is
positive in the coefficient algebra. -/
theorem moduleGram_quadratic_nonneg (s : Finset ι) (x : ι → E) (b : ι → B) :
    (0 : B) ≤ ∑ i ∈ s, ∑ j ∈ s,
      star (b i) * MulOpposite.unop ⟪x i, x j⟫_(Bᵐᵒᵖ) * b j := by
  rw [moduleGram_quadratic_eq_inner]
  exact MulOpposite.unop_nonneg.mpr CStarModule.inner_self_nonneg

end BC4lean.KKTheory
