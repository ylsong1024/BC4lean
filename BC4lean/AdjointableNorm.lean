import BC4lean.AdjointableOperator

/-! # Operator norms of adjointable maps

The adjoint preserves the operator norm, and adjointable maps satisfy the
C⋆-identity for the coefficient-valued inner product. These results hold for
pre-Hilbert modules as well as complete Hilbert modules, over nonunital
coefficient algebras. At this layer the norm is written on `toCLM` explicitly.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {B E F G : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]

namespace AdjointableMap

/-- The usual operator norm bound for application. -/
theorem norm_apply_le (T : AdjointableMap B E F) (x : E) :
    ‖T x‖ ≤ ‖T.toCLM‖ * ‖x‖ := T.toCLM.le_opNorm x

/-- Composition is submultiplicative for the operator norm. -/
theorem norm_toCLM_comp_le (S : AdjointableMap B F G) (T : AdjointableMap B E F) :
    ‖(S.comp T).toCLM‖ ≤ ‖S.toCLM‖ * ‖T.toCLM‖ :=
  ContinuousLinearMap.opNorm_comp_le S.toCLM T.toCLM

/-- The coefficient-valued inner product identifies the squared image norm. -/
theorem norm_sq_eq_inner_adjoint_comp (T : AdjointableMap B E F) (x : E) :
    ‖T x‖ ^ 2 = ‖⟪x, T.adjoint.comp T x⟫_(Bᵐᵒᵖ)‖ := by
  change ‖T x‖ ^ 2 = ‖⟪x, T.adjointCLM (T x)⟫_(Bᵐᵒᵖ)‖
  rw [CStarModule.norm_sq_eq (Bᵐᵒᵖ), T.adjoint_identity]

variable [StarOrderedRing B]

/-- The squared norm of an image is bounded using the adjoint. -/
theorem norm_sq_le_adjoint_mul (T : AdjointableMap B E F) (x : E) :
    ‖T x‖ ^ 2 ≤ (‖T.adjointCLM‖ * ‖x‖) * ‖T x‖ := by
  calc
    ‖T x‖ ^ 2 = ‖⟪T x, T x⟫_(Bᵐᵒᵖ)‖ := CStarModule.norm_sq_eq (Bᵐᵒᵖ)
    _ = ‖⟪x, T.adjointCLM (T x)⟫_(Bᵐᵒᵖ)‖ := by rw [T.adjoint_identity]
    _ ≤ ‖x‖ * ‖T.adjointCLM (T x)‖ := CStarModule.norm_inner_le E
    _ ≤ ‖x‖ * (‖T.adjointCLM‖ * ‖T x‖) := by
      exact mul_le_mul_of_nonneg_left (T.adjointCLM.le_opNorm (T x)) (_root_.norm_nonneg x)
    _ = (‖T.adjointCLM‖ * ‖x‖) * ‖T x‖ := by ring

/-- An adjoint also gives a bound on every image. -/
theorem norm_apply_le_adjoint_mul (T : AdjointableMap B E F) (x : E) :
    ‖T x‖ ≤ ‖T.adjointCLM‖ * ‖x‖ := by
  by_cases h : ‖T x‖ = 0
  · rw [h]
    positivity
  · have hpos : 0 < ‖T x‖ := lt_of_le_of_ne (_root_.norm_nonneg _) (Ne.symm h)
    exact le_of_mul_le_mul_right (by
      simpa only [pow_two] using norm_sq_le_adjoint_mul T x) hpos

/-- The norm of a map is bounded by the norm of its adjoint. -/
theorem norm_toCLM_le_adjointCLM (T : AdjointableMap B E F) :
    ‖T.toCLM‖ ≤ ‖T.adjointCLM‖ :=
  T.toCLM.opNorm_le_bound (_root_.norm_nonneg _) (norm_apply_le_adjoint_mul T)

/-- Taking the adjoint preserves the operator norm. -/
@[simp] theorem norm_adjointCLM (T : AdjointableMap B E F) :
    ‖T.adjointCLM‖ = ‖T.toCLM‖ := by
  exact le_antisymm (norm_toCLM_le_adjointCLM T.adjoint) (norm_toCLM_le_adjointCLM T)

/-- The norm of the underlying bounded map of the adjoint. -/
@[simp] theorem norm_adjoint_toCLM (T : AdjointableMap B E F) :
    ‖T.adjoint.toCLM‖ = ‖T.toCLM‖ := norm_adjointCLM T

/-- Taking adjoints preserves the norm of the difference of bounded maps. -/
theorem norm_adjointCLM_sub (S T : AdjointableMap B E F) :
    ‖S.adjointCLM - T.adjointCLM‖ = ‖S.toCLM - T.toCLM‖ := by
  simpa [AdjointableMap.add, AdjointableMap.smul, sub_eq_add_neg] using
    norm_adjointCLM (S.add (T.smul (-1)))

/-- Adjoint norm preservation for differences, phrased using `toCLM`. -/
theorem norm_adjoint_toCLM_sub (S T : AdjointableMap B E F) :
    ‖S.adjoint.toCLM - T.adjoint.toCLM‖ = ‖S.toCLM - T.toCLM‖ :=
  norm_adjointCLM_sub S T

/-- The pointwise estimate underlying the C⋆-identity. -/
theorem norm_sq_le_adjoint_comp (T : AdjointableMap B E F) (x : E) :
    ‖T x‖ ^ 2 ≤ ‖(T.adjoint.comp T).toCLM‖ * ‖x‖ ^ 2 := by
  calc
    ‖T x‖ ^ 2 = ‖⟪x, T.adjoint.comp T x⟫_(Bᵐᵒᵖ)‖ := norm_sq_eq_inner_adjoint_comp T x
    _ ≤ ‖x‖ * ‖T.adjoint.comp T x‖ := CStarModule.norm_inner_le E
    _ ≤ ‖x‖ * (‖(T.adjoint.comp T).toCLM‖ * ‖x‖) := by
      exact mul_le_mul_of_nonneg_left (norm_apply_le _ x) (_root_.norm_nonneg x)
    _ = ‖(T.adjoint.comp T).toCLM‖ * ‖x‖ ^ 2 := by ring

/-- A square-root operator bound obtained from `T* T`. -/
theorem norm_apply_le_sqrt_adjoint_comp (T : AdjointableMap B E F) (x : E) :
    ‖T x‖ ≤ Real.sqrt ‖(T.adjoint.comp T).toCLM‖ * ‖x‖ := by
  calc
    ‖T x‖ = Real.sqrt (‖T x‖ ^ 2) := (Real.sqrt_sq (_root_.norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖(T.adjoint.comp T).toCLM‖ * ‖x‖ ^ 2) :=
      Real.sqrt_le_sqrt (norm_sq_le_adjoint_comp T x)
    _ = Real.sqrt ‖(T.adjoint.comp T).toCLM‖ * ‖x‖ := by
      rw [Real.sqrt_mul (_root_.norm_nonneg _), Real.sqrt_sq (_root_.norm_nonneg _)]

/-- The C⋆-identity for adjointable maps, including maps between different modules. -/
theorem norm_toCLM_adjoint_comp_self (T : AdjointableMap B E F) :
    ‖(T.adjoint.comp T).toCLM‖ = ‖T.toCLM‖ ^ 2 := by
  apply le_antisymm
  · calc
      ‖(T.adjoint.comp T).toCLM‖ ≤ ‖T.adjoint.toCLM‖ * ‖T.toCLM‖ := norm_toCLM_comp_le _ _
      _ = ‖T.toCLM‖ ^ 2 := by rw [norm_adjoint_toCLM, pow_two]
  · have h : ‖T.toCLM‖ ≤ Real.sqrt ‖(T.adjoint.comp T).toCLM‖ :=
      T.toCLM.opNorm_le_bound (Real.sqrt_nonneg _) (norm_apply_le_sqrt_adjoint_comp T)
    have hsq := pow_le_pow_left₀ (_root_.norm_nonneg T.toCLM) h 2
    simpa only [Real.sq_sqrt (_root_.norm_nonneg _)] using hsq

/-- The C⋆-identity with the two factors in the other order. -/
theorem norm_toCLM_self_comp_adjoint (T : AdjointableMap B E F) :
    ‖(T.comp T.adjoint).toCLM‖ = ‖T.toCLM‖ ^ 2 := by
  simpa only [adjoint_adjoint, norm_adjoint_toCLM] using
    norm_toCLM_adjoint_comp_self T.adjoint

end AdjointableMap
end BC4lean.KKTheory
