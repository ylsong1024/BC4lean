import BC4lean.AdjointableComplete
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Positive actual module operators and their coefficient forms

Positive elements of the actual complete adjointable endomorphism algebra
give positive coefficient forms. The proof uses the star-square order
construction, not a Hilbert-space representation. Applying it to the norm
defect gives the coefficient-order operator norm bound needed for genuine
countable module diagonals.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

local instance moduleOperatorPositivityPartialOrder : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance moduleOperatorPositivityStarOrderedRing : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

namespace AdjointableMap

/-- Actual positive adjointable maps induce positive coefficient forms. -/
theorem inner_nonneg_of_nonneg (T : AdjointableMap B E E) (hT : 0 ≤ T) (y : E) :
    0 ≤ ⟪y, T y⟫_(Bᵐᵒᵖ) := by
  rw [StarOrderedRing.nonneg_iff] at hT
  induction hT using AddSubmonoid.closure_induction with
  | mem T hT =>
    obtain ⟨S, rfl⟩ := hT
    change 0 ≤ ⟪y, S.adjointCLM (S y)⟫_(Bᵐᵒᵖ)
    rw [← S.adjoint_identity]
    exact CStarModule.inner_self_nonneg
  | zero => simp
  | add T U _ _ ihT ihU =>
    simpa only [coe_add_apply, CStarModule.inner_add_right] using add_nonneg ihT ihU

/-- The actual norm-square defect gives the coefficient-order norm bound. -/
theorem inner_self_apply_le (T : AdjointableMap B E E) (y : E) :
    ⟪T y, T y⟫_(Bᵐᵒᵖ) ≤ (‖T‖ ^ 2 : ℝ) • ⟪y, y⟫_(Bᵐᵒᵖ) := by
  have hD : 0 ≤ algebraMap ℝ (AdjointableMap B E E) (‖T‖ ^ 2) - star T * T :=
    sub_nonneg.mpr CStarAlgebra.star_mul_le_algebraMap_norm_sq
  have h := inner_nonneg_of_nonneg _ hD y
  have hreal : algebraMap ℝ (AdjointableMap B E E) (‖T‖ ^ 2) =
      ((‖T‖ ^ 2 : ℝ) : ℂ) • (1 : AdjointableMap B E E) := by
    rw [Algebra.algebraMap_eq_smul_one]
    rfl
  rw [hreal, coe_sub_apply, coe_smul_apply, one_apply, mul_apply, star_eq_adjoint,
    CStarModule.inner_sub_right, CStarModule.inner_smul_right_complex] at h
  change 0 ≤ ((‖T‖ ^ 2 : ℝ) : ℂ) • ⟪y, y⟫_(Bᵐᵒᵖ) -
    ⟪y, T.adjointCLM (T y)⟫_(Bᵐᵒᵖ) at h
  rw [← T.adjoint_identity] at h
  exact sub_nonneg.mp h

end AdjointableMap
end BC4lean.KKTheory
