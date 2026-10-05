import BC4lean.BalancedModuleTensor
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-! # The interior-tensor pairing on elementary tensors

For a right Hilbert B-module E and a left B-action by adjointable maps on a
right Hilbert C-module F, the elementary pairing is
`⟨x ⊗ y, x' ⊗ y'⟩ = ⟨y, φ(⟨x,x'⟩)y'⟩`.

Its balancing, Hermitian symmetry, elementary positivity and norm bound are
proved here.  Positivity on arbitrary sums of elementary tensors is a further
statement, not an assumption or a conclusion of this file.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace
open CStarModule

variable {B C E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [PartialOrder C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]

/-- The expected C-valued elementary interior-tensor pairing, expressed in the
opposite coefficient convention used for right modules. -/
def moduleTensorPureInner (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (x : E) (y : F) (x' : E) (y' : F) : Cᵐᵒᵖ :=
  ⟪y, φ (MulOpposite.unop ⟪x, x'⟫_(Bᵐᵒᵖ)) y'⟫_(Cᵐᵒᵖ)

@[simp] theorem moduleTensorPureInner_add_first
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x u x' : E) (y y' : F) :
    moduleTensorPureInner φ (x + u) y x' y' =
      moduleTensorPureInner φ x y x' y' + moduleTensorPureInner φ u y x' y' := by
  simp only [moduleTensorPureInner, CStarModule.inner_add_left, MulOpposite.unop_add, map_add,
    AdjointableMap.coe_add_apply, CStarModule.inner_add_right]

@[simp] theorem moduleTensorPureInner_smul_first
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (c : ℂ) (x x' : E) (y y' : F) :
    moduleTensorPureInner φ (c • x) y x' y' = star c • moduleTensorPureInner φ x y x' y' := by
  simp only [moduleTensorPureInner, inner_smul_left_complex, MulOpposite.unop_smul,
    map_smul, AdjointableMap.coe_smul_apply, inner_smul_right_complex]

@[simp] theorem moduleTensorPureInner_add_second
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x x' : E) (y v y' : F) :
    moduleTensorPureInner φ x (y + v) x' y' =
      moduleTensorPureInner φ x y x' y' + moduleTensorPureInner φ x v x' y' := by
  exact CStarModule.inner_add_left

@[simp] theorem moduleTensorPureInner_smul_second
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (c : ℂ) (x x' : E) (y y' : F) :
    moduleTensorPureInner φ x (c • y) x' y' = star c • moduleTensorPureInner φ x y x' y' := by
  exact inner_smul_left_complex

@[simp] theorem moduleTensorPureInner_add_third
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x x' u' : E) (y y' : F) :
    moduleTensorPureInner φ x y (x' + u') y' =
      moduleTensorPureInner φ x y x' y' + moduleTensorPureInner φ x y u' y' := by
  simp only [moduleTensorPureInner, CStarModule.inner_add_right, MulOpposite.unop_add, map_add,
    AdjointableMap.coe_add_apply]

@[simp] theorem moduleTensorPureInner_smul_third
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (c : ℂ) (x x' : E) (y y' : F) :
    moduleTensorPureInner φ x y (c • x') y' = c • moduleTensorPureInner φ x y x' y' := by
  simp only [moduleTensorPureInner, inner_smul_right_complex, MulOpposite.unop_smul,
    map_smul, AdjointableMap.coe_smul_apply]

@[simp] theorem moduleTensorPureInner_add_fourth
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x x' : E) (y y' v' : F) :
    moduleTensorPureInner φ x y x' (y' + v') =
      moduleTensorPureInner φ x y x' y' + moduleTensorPureInner φ x y x' v' := by
  change ⟪y, (φ (MulOpposite.unop ⟪x, x'⟫_(Bᵐᵒᵖ))).toCLM (y' + v')⟫_(Cᵐᵒᵖ) = _
  rw [map_add, CStarModule.inner_add_right]
  rfl

@[simp] theorem moduleTensorPureInner_smul_fourth
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (c : ℂ) (x x' : E) (y y' : F) :
    moduleTensorPureInner φ x y x' (c • y') = c • moduleTensorPureInner φ x y x' y' := by
  change ⟪y, (φ (MulOpposite.unop ⟪x, x'⟫_(Bᵐᵒᵖ))).toCLM (c • y')⟫_(Cᵐᵒᵖ) = _
  rw [map_smul, inner_smul_right_complex]
  rfl

/-- The pairing respects the coefficient-balancing relation in its first
tensor variable. -/
theorem moduleTensorPureInner_balance_left
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (b : B) (x x' : E) (y y' : F) :
    moduleTensorPureInner φ (MulOpposite.op b • x) y x' y' =
      moduleTensorPureInner φ x (φ b y) x' y' := by
  unfold moduleTensorPureInner
  rw [inner_op_smul_left, MulOpposite.unop_mul, MulOpposite.unop_star,
    MulOpposite.unop_op, map_mul, map_star]
  exact ((φ b).adjoint_identity y (φ (MulOpposite.unop ⟪x, x'⟫_(Bᵐᵒᵖ)) y')).symm

/-- The pairing respects the coefficient-balancing relation in its second
tensor variable. -/
theorem moduleTensorPureInner_balance_right
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (b : B) (x x' : E) (y y' : F) :
    moduleTensorPureInner φ x y (MulOpposite.op b • x') y' =
      moduleTensorPureInner φ x y x' (φ b y') := by
  unfold moduleTensorPureInner
  simp only [inner_op_smul_right, MulOpposite.unop_mul, MulOpposite.unop_op,
    map_mul, AdjointableMap.mul_apply]

/-- Hermitian symmetry of the elementary interior-tensor pairing. -/
theorem moduleTensorPureInner_star
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x x' : E) (y y' : F) :
    star (moduleTensorPureInner φ x y x' y') = moduleTensorPureInner φ x' y' x y := by
  unfold moduleTensorPureInner
  rw [star_inner, (φ (MulOpposite.unop ⟪x, x'⟫_(Bᵐᵒᵖ))).adjoint_identity]
  change ⟪y', star (φ (MulOpposite.unop ⟪x, x'⟫_(Bᵐᵒᵖ))) y⟫_(Cᵐᵒᵖ) = _
  rw [← map_star, ← MulOpposite.unop_star, star_inner]

variable [StarOrderedRing B]

/-- Elementary tensor positivity is proved by factorizing the positive
coefficient inner product with the non-unital continuous functional calculus.
No positivity of the tensor pairing is assumed. -/
theorem moduleTensorPureInner_self_nonneg
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x : E) (y : F) :
    0 ≤ moduleTensorPureInner φ x y x y := by
  let a : B := MulOpposite.unop ⟪x, x⟫_(Bᵐᵒᵖ)
  have ha : 0 ≤ a := MulOpposite.unop_nonneg.mpr inner_self_nonneg
  have hfactor : a = star (CFC.sqrt a) * CFC.sqrt a := by
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq]
    exact (CFC.sqrt_mul_sqrt_self a ha).symm
  change 0 ≤ ⟪y, φ a y⟫_(Cᵐᵒᵖ)
  rw [hfactor, map_mul, map_star]
  change 0 ≤ ⟪y, (φ (CFC.sqrt a)).adjointCLM ((φ (CFC.sqrt a)) y)⟫_(Cᵐᵒᵖ)
  rw [← (φ (CFC.sqrt a)).adjoint_identity]
  exact inner_self_nonneg

variable [StarOrderedRing C] [CompleteSpace F]

/-- A four-factor norm bound for the elementary coefficient pairing. -/
theorem moduleTensorPureInner_norm_le
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x x' : E) (y y' : F) :
    ‖moduleTensorPureInner φ x y x' y'‖ ≤ ‖x‖ * ‖y‖ * ‖x'‖ * ‖y'‖ := by
  have hφ : ‖(φ (MulOpposite.unop ⟪x, x'⟫_(Bᵐᵒᵖ))).toCLM‖ ≤
      ‖⟪x, x'⟫_(Bᵐᵒᵖ)‖ := by
    simpa only [AdjointableMap.norm_def, MulOpposite.norm_unop] using
      NonUnitalStarAlgHom.norm_apply_le φ (MulOpposite.unop ⟪x, x'⟫_(Bᵐᵒᵖ))
  calc
    ‖moduleTensorPureInner φ x y x' y'‖ ≤
        ‖y‖ * ‖φ (MulOpposite.unop ⟪x, x'⟫_(Bᵐᵒᵖ)) y'‖ := norm_inner_le F
    _ ≤ ‖y‖ * (‖(φ (MulOpposite.unop ⟪x, x'⟫_(Bᵐᵒᵖ))).toCLM‖ * ‖y'‖) :=
      mul_le_mul_of_nonneg_left (AdjointableMap.norm_apply_le _ _) (_root_.norm_nonneg y)
    _ ≤ ‖y‖ * (‖⟪x, x'⟫_(Bᵐᵒᵖ)‖ * ‖y'‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hφ (_root_.norm_nonneg y')) (_root_.norm_nonneg y)
    _ ≤ ‖y‖ * ((‖x‖ * ‖x'‖) * ‖y'‖) := by
      gcongr
      exact norm_inner_le E
    _ = ‖x‖ * ‖y‖ * ‖x'‖ * ‖y'‖ := by ring

end BC4lean.KKTheory
