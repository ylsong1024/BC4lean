import BC4lean.CompactModuleOperator
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-! # Complex Hilbert spaces as right scalar Hilbert C⋆-modules

The scoped instances below put a `CStarModule ℂᵐᵒᵖ H` structure on the
existing complex inner product space `H`. Its action is ordinary scalar
multiplication through `MulOpposite.unop`, and its coefficient-valued inner
product is the opposite of the usual, second-linear complex inner product.
The norm, topology, and completeness are the existing Hilbert-space ones.

Bounded Hilbert-space maps with adjoints therefore give actual adjointable
module maps. For a complete target, module compactness implies ordinary
Hilbert-space compactness: scalar module rank-one maps factor through ℂ,
and the ordinary compact operators are closed in the operator norm.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace ComplexOrder

namespace ScalarHilbertModule

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Right complex scalar multiplication, expressed using opposite scalars. -/
scoped instance instSMulOpposite : SMul ℂᵐᵒᵖ H where
  smul a x := MulOpposite.unop a • x

open scoped ScalarHilbertModule

@[simp] theorem op_smul (a : ℂ) (x : H) : MulOpposite.op a • x = a • x := rfl

@[simp] theorem unop_smul (a : ℂᵐᵒᵖ) (x : H) : a • x = MulOpposite.unop a • x := rfl

/-- The scalar Hilbert-module structure uses the existing Hilbert norm. -/
scoped instance instCStarModule : CStarModule ℂᵐᵒᵖ H where
  inner x y := MulOpposite.op ⟪x, y⟫_ℂ
  inner_add_right := by
    intro x y z
    apply MulOpposite.unop_injective
    exact _root_.inner_add_right x y z
  inner_self_nonneg {x} := by
    change (0 : ℂ) ≤ ⟪x, x⟫_ℂ
    rw [← inner_self_ofReal_re, RCLike.ofReal_nonneg]
    exact _root_.inner_self_nonneg
  inner_self {x} := by
    change MulOpposite.op ⟪x, x⟫_ℂ = MulOpposite.op (0 : ℂ) ↔ x = 0
    rw [MulOpposite.op_inj]
    exact _root_.inner_self_eq_zero
  inner_op_smul_right {a x y} := by
    apply MulOpposite.unop_injective
    change ⟪x, MulOpposite.unop a • y⟫_ℂ = ⟪x, y⟫_ℂ * MulOpposite.unop a
    rw [_root_.inner_smul_right, mul_comm]
  inner_smul_right_complex {z x y} := by
    apply MulOpposite.unop_injective
    change ⟪x, z • y⟫_ℂ = z • ⟪x, y⟫_ℂ
    simp only [_root_.inner_smul_right, smul_eq_mul]
  star_inner x y := by
    apply MulOpposite.unop_injective
    change star ⟪x, y⟫_ℂ = ⟪y, x⟫_ℂ
    exact _root_.inner_conj_symm y x
  norm_eq_sqrt_norm_inner_self x := by
    simpa only [MulOpposite.norm_op, ← inner_self_re_eq_norm] using
      (norm_eq_sqrt_re_inner (𝕜 := ℂ) x)

@[simp] theorem inner_eq_op (x y : H) :
    ⟪x, y⟫_(ℂᵐᵒᵖ) = MulOpposite.op ⟪x, y⟫_ℂ := rfl

@[simp] theorem unop_inner (x y : H) :
    MulOpposite.unop ⟪x, y⟫_(ℂᵐᵒᵖ) = ⟪x, y⟫_ℂ := rfl

/-- A bounded Hilbert-space map with a specified bounded adjoint is an
adjointable right scalar module map. -/
def ofAdjointPair (T : H →L[ℂ] K) (S : K →L[ℂ] H)
    (h : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, S y⟫_ℂ) : AdjointableMap ℂ H K where
  toCLM := T
  adjointCLM := S
  adjoint_identity x y := congrArg MulOpposite.op (h x y)

@[simp] theorem ofAdjointPair_toCLM (T : H →L[ℂ] K) (S : K →L[ℂ] H)
    (h : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, S y⟫_ℂ) :
    (ofAdjointPair T S h).toCLM = T := rfl

@[simp] theorem ofAdjointPair_adjointCLM (T : H →L[ℂ] K) (S : K →L[ℂ] H)
    (h : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, S y⟫_ℂ) :
    (ofAdjointPair T S h).adjointCLM = S := rfl

/-- Every bounded map between complete complex Hilbert spaces embeds into
the scalar-module adjointable maps, with its usual Hilbert adjoint. -/
def ofContinuousLinearMap [CompleteSpace H] [CompleteSpace K] (T : H →L[ℂ] K) :
    AdjointableMap ℂ H K :=
  ofAdjointPair T T.adjoint (fun x y =>
    (ContinuousLinearMap.adjoint_inner_right T x y).symm)

@[simp] theorem ofContinuousLinearMap_toCLM [CompleteSpace H] [CompleteSpace K]
    (T : H →L[ℂ] K) : (ofContinuousLinearMap T).toCLM = T := rfl

@[simp] theorem ofContinuousLinearMap_adjointCLM [CompleteSpace H] [CompleteSpace K]
    (T : H →L[ℂ] K) : (ofContinuousLinearMap T).adjointCLM = T.adjoint := rfl

@[simp] theorem ofContinuousLinearMap_norm [CompleteSpace H] [CompleteSpace K]
    (T : H →L[ℂ] K) : ‖ofContinuousLinearMap T‖ = ‖T‖ := rfl

/-- In the scalar case a module rank-one map factors through the
one-dimensional Hilbert space ℂ. -/
theorem moduleRankOne_toCLM (x : K) (y : H) :
    (moduleRankOne (B := ℂ) x y).toCLM =
      (ContinuousLinearMap.toSpanSingleton ℂ x).comp (innerSL ℂ y) := by
  ext z
  rfl

/-- Scalar module rank-one maps are compact Hilbert-space operators. -/
theorem moduleRankOne_isCompactOperator (x : K) (y : H) :
    IsCompactOperator (moduleRankOne (B := ℂ) x y).toCLM := by
  rw [moduleRankOne_toCLM]
  exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℂ y)).clm_comp
    (ContinuousLinearMap.toSpanSingleton ℂ x)

/-- For a complete target the norm closure of scalar module rank-one maps
consists of compact Hilbert-space operators. -/
theorem isCompactOperator_of_isModuleCompact [CompleteSpace K]
    {T : AdjointableMap ℂ H K} (hT : IsModuleCompact T) : IsCompactOperator T.toCLM := by
  let S : Submodule ℂ (AdjointableMap ℂ H K) :=
    (compactOperator (RingHom.id ℂ) H K).comap AdjointableMap.toCLMLinearMap
  have hS : IsClosed (S : Set (AdjointableMap ℂ H K)) :=
    isClosed_setOfPred_isCompactOperator.preimage
      AdjointableMap.toCLMContinuousLinearMap.continuous
  have hθ : ∀ (x : K) (y : H), moduleRankOne (B := ℂ) x y ∈ S :=
    fun x y => moduleRankOne_isCompactOperator x y
  exact moduleCompact_le_of_isClosed S hS hθ hT

end ScalarHilbertModule
end BC4lean.KKTheory
